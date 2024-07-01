import galois
import numpy as np
import random as rand

rand.seed()



prima = 2 ## prime
orda = 3 ## prime power
fOrd = prima**orda   #field order
## o = 3 D = 2 gives three codewords 
## o = 4 D = 2 gives an insane amount
## o = 4 D = 3 gives 15 codewords

gPolDeg = 2 ## degree of goppa polynomial
## Since the degree of the goppa polynomial increases the weight of codeword it makes far less vectors viable 
## how does this impact security and other aspects of the cryptosystem?
## the smaller the degree is the less values of the message vector we can hide


GF = galois.GF(prima, orda, repr="poly") ##defining our finite field

###increase code support size minize goppa degree for maximum amount of codewords.



print(GF.properties)
print(GF.elements)



goppaPol = galois.irreducible_poly(fOrd, gPolDeg ) ## find irreducible polynomial with degree gPolDeg ##goppa polynomial

print("goppa polynomial: ",goppaPol)

codeSupportPol = []     ## list of polynomials used in defining the syndrome
codeSupportPolInv = []  ## their inverses
coefffield = []         ##list of coefficient for each polynomial of the syndrome used for finding valid codevectors in our goppa code
for i in range(fOrd):
    codeSupportPol.append(galois.Poly([1, i], field=GF))
    # print(codeSupportPol[i])
    codeSupportPolInv.append(galois.egcd(codeSupportPol[i], goppaPol)[1])
    # print(codeSupportPolInv[i])
    coefffield.append(codeSupportPolInv[i].coefficients())
    



coefffield = GF(coefffield)
# print("coefficients for inverse polynomials.")
# print(coefffield)



bb = 0b00
##help function used in generating every vector in our vectorspace
def bin2GF(bb):
    arr = np.zeros(fOrd, int)
    for i in range(len(arr)):  
        if bb % 2 == 1:
            arr[fOrd-1 - i] = 1  
        bb >>= 1  
    return arr

def hammingWeight(arr):
    w = 0
    for i in arr:
        if i == 1:
            w += 1
    return w

goppaCodes = []  ## valid goppa codevectors
err_vec = [] ## valid error vectors

## this for loop fills our above vectors
zeroMat = np.zeros(gPolDeg, int)
# print("goppa codewords")
for i in range(0, 2**fOrd):##list all c vectors such that goppa condition satisfied
    arr = GF(bin2GF(bb))
    kk = np.matmul(coefffield.transpose(), arr)
    if (kk==zeroMat).all():
        # print(kk)
        print(arr)
        goppaCodes.append(arr)
    elif (hammingWeight(arr) == gPolDeg):
        err_vec.append(arr)

    bb += 1

# print(goppaCodes)
# print(err_vec)

##not really eea
def extended_euclidean_algorithm(g, tau, t):
    i = 0
    r = [g, tau]
    alpha = [g, tau]
    beta = [galois.Poly([0], GF), galois.Poly([1], GF)]

    while r[i].degree >= (t + 1) // 2:
        i += 1
        q, r_i = divmod(r[i-1], r[i-2])
        r.append(r_i)
        beta.append(beta[i-2] + q * beta[i-1])
        alpha.append(r[i])

    return alpha[i], beta[i]

def pattersons(notcodeword):
    syndrome = np.matmul(coefffield.transpose(), notcodeword)
    if (syndrome == zeroMat).all():
        return (notcodeword, 0)
    else:
        syndrome = galois.Poly(syndrome)  
        T = galois.egcd(syndrome, goppaPol)[1]
        Tpx = T +galois.Poly([1,0], GF)
        tau = 0
        # tauS2 = 0
        # i = 0
        # while Tpx != tauS2: #fix this, the order thing online is wrong i = 32 not prima**(orda-1) probably ford**gpoldeg instead
        #     tau = pow(Tpx, i, goppaPol)
        #     tauS2 = pow(tau, 2, goppaPol)#
        #     print( tauS2, i)
        #     i += 1

        for i in range(fOrd**gPolDeg):
            tau = pow(Tpx, i, goppaPol)
            if pow(tau, 2, goppaPol) == Tpx:
                #print(tau)
                break

        alpha, beta = extended_euclidean_algorithm(goppaPol, tau, gPolDeg)
        alpha_squared = pow(alpha,2)
        beta_squared = pow(beta,2)
        x = galois.Poly([1, 0], GF)

        sigma =  (alpha_squared + x * beta_squared) 


        leading_coeff = sigma.coeffs[0]  
        c = 0
        for i in GF.elements:
            if leading_coeff* i == 1:
                c = i
                break
        #print(c)
        sigma =c*sigma
        
        # sigma, _ = divmod(sigma, galois.Poly([leading_coeff], GF))  
        # print(sigma)
        # sigma = sigma  % goppaPol
        # print(sigma.roots())

        e = np.zeros(len(err_vec[0]), int)
        for i in range(len(err_vec[0])):
            if sigma.__call__(GF(i)) == 0:  
                e[i] = 1

        e = GF(e)
        #print(e)
        m = notcodeword + e
        #print(m)
        return  m, e


# print(goppaCodes[3])
# print(err_vec[4])
# nc = goppaCodes[3]+err_vec[4] 
# print(nc)


# pattersons(nc)

S=[[1,1],[0,1]]
P = [[0,0,0,0,1,0,0,0],[0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1],[0,1,0,0,0,0,0,0], [0,0,0,1,0,0,0,0], [1,0,0,0,0,0,0,0],[0,0,0,0,0,1,0,0],[0,0,1,0,0,0,0,0]] 
G = [[0,0,0,1,1,1,1,1,],[1,1,0,1,0,1,0,1]]
g_pub= [[0,0,0,1,1,1,1,1,],[1,1,1,0,1,0,1,0]]
k = len(G)
G = GF(G)
S = GF(S)


## Converts a string into an binary array
def str_to_binary(text):
    # Convert the text to binary
    binary_text = ''.join(format(ord(char), '08b') for char in text)

    # Convert the binary string to an array of integers
    binary_array = [int(bit) for bit in binary_text]

    return np.array(binary_array)


def encrypt(g_pub, binary_plaintext, add_error):
    
    c_arr = []
    binary_plaintext = GF(binary_plaintext)
    g_pub = GF(g_pub)
    ## we multiply k bits to our public key at a time and add the encrypted bits to an array.
    for i in range(0, len(binary_plaintext),k):
        c_arr.append((binary_plaintext[i:i+k]@ g_pub))
        
    randint = rand.randint(1,len(err_vec)-1) ## cant use a new one for every k bits
    ##now we add an error vector to the vectors ## maybe take random err vector every time.

    c_arr_err= [(i+add_error) for i in c_arr]
    return c_arr_err
    


def information_set(G):
    while True:
        k = len(G) ## verify this ##verified
        I = []
        ## Tries a random I until G_.I is invertible.  Meaning the determinant is nonzero.
        while True:
            I = rand.sample(population=range(1,fOrd),k=k)
            
            gSub =  G[:,I]
            if np.linalg.det(gSub) != 0:
                return I
            
            
def decrypt(G,S,P, c_arr_err):
    ## we multiply with the inverse of the permutation matrix
    c_arr_err = c_arr_err@np.linalg.inv(P)

    c_arr_err = GF(c_arr_err.astype(int))

    ##remove error vector
    decoded_c_arr =[]
    for i in range(len(c_arr_err)):
        plup,_ = pattersons(c_arr_err[i])
        decoded_c_arr.append(plup)
        
    ## we have to find an index set such that G_.I is invertible
    I  = information_set(G)

    ## now we revert our ciphertext 
    GInv = GF(np.linalg.inv(G[:,I]).astype(np.int32))
    SInv = GF(np.linalg.inv(S).astype(np.int32))

    c_arr_rev =[i[I]@GInv@SInv for i in decoded_c_arr]
    return c_arr_rev



text = "Hello! My name is."
#### "Hello! My name is."
#### 01001000 01100101 01101100 01101100 01101111 00100001 00100000 01001101 01111001 00100000 01101110 01100001 01101101 01100101 00100000 01101001 01110011 00101110 

binary_array = str_to_binary(text)

c_arr_err = encrypt(g_pub, binary_array, err_vec[3])


cArrRev = decrypt(G,S,P,c_arr_err)

## we compare to the original plaintext for verification
plainConcat = np.reshape(cArrRev,binary_array.shape)
print("plain binary", plainConcat)



print("asda",chr(72))



def bin_2_str(int_array):
    #convert int array to sets of binary values
    bin_int_array = []
    for i in range(0,len(plainConcat),8):
        bla =0
        for j in range(8):
            bla = bla +(2**(7-j))*plainConcat[i+j]
        bin_int_array.append(bla)
                
    chr_arr = []
    for i in bin_int_array:
        chr_arr.append(chr(i))
        
    plain_text = "".join(i for i in chr_arr)
    return plain_text
    



## with this we have taken a plaintext written it in binary using the ascii/utf8 encoding into an array, taken k bits of the array at a time and encoded with the public key and later reverted it.
## TODO: add error vector and remove using the pattersons algorithm.
## Bug: will only work for congruent length of array modulo k. this is not an issue for our purposes, to keep code in line stick with ascii and have k be 2,4 or 8. can be fixed with padding.



################GISD
## Generalized Information set decoding
## G is a random binary kxn matrix
## c =mG+e is a cipher hiding our plaintext
## integer j, j <= t ## t is in the public key

def GISD(G, c, j, t): ### this code is not completing, make sure it works.
    while True:
        k = len(G) 
        c = GF(c)
        I = information_set(G)

        Q_1 =GF(np.linalg.inv(G[:,I]))
        Q_2 = GF(Q_1@G)
        z = c + (c[:,I]@Q_2) 
        
        for i in range(j+1):
            for e in err_vec[:5]:
                if np.sum(np.take(e,I)) == i and np.sum(z + np.take(e,I)@Q_2) == t:
                    return (c[:,I]+np.take(e,I))@Q_1 
                
#print("errorvector",err_vec[4])
#text = "Hello! My name is."
#### "Hello! My name is."
#### 01001000 01100101 01101100 01101100 01101111 00100001 00100000 01001101 01111001 00100000 01101110 01100001 01101101 01100101 00100000 01101001 01110011 00101110 

##binary_array = str_to_binary(text)

##c_arr_err = encrypt(g_pub, binary_array)
##cArrRev = GISD(G,c_arr_err,1,2)

## we compare to the original plaintext for verification
#plainConcat = np.reshape(cArrRev,binary_array.shape)
#print(plainConcat == binary_array)
##TODO: random matrix generator and generalize reused code in functions,

        
#print(len(G[0]))      
def stern(G, t, p, l):
    I = information_set(G)
    N = np.arange(len(G[0]))
    NsI = np.delete(N,I)
    K = np.arange(len(G))

    ## TODO: define P and G_r,c
    P = []
    KsP =  np.delete(K,P)
    for i in range(1,k):
        K = np.arange(len(G))
        



######## ind-cca2 for original mceliece
    
plain_1 = goppaCodes[3]
plain_2 = goppaCodes[2]


ciph = GF(encrypt(G, plain_1, err_vec[3]))


#print("test parameters")
print("plain_1", plain_1)
print("plain_2", plain_2)
print("ciph", ciph)
#print("error", err_vec[3])
#print("G",G)
zero_err_vec = GF([0,0,0,0,0,0,0,0])

## testing against the indcca2 attackmodel
def ind_cca2(G,c, m1, m2):
    #print("encrypt m1 with 0 errors",GF(encrypt(G, m2, zero_err_vec)))
    m1 = encrypt(G, m1, zero_err_vec)
    m1 = GF(m1)    
    m2 = encrypt(G, m2, zero_err_vec)
    m2 = GF(m2)
    su = [0,0,0,0]
    sa = [0,0,0,0]
    
    for i in range(len(c- m1)): ##np.sum not working as expected
        for j in (c- m1)[i]:
            if j == 1:
                su[i] = su[i] +  1
                
    for i in range(len(c- m2)): ##np.sum not working as expected
        for j in (c- m2)[i]:
            if j == 1:
                sa[i] = sa[i] +  1
    
    def check_something(sasa):
        for i in sasa:
            if i != gPolDeg:
                return False
        return True 
    print(check_something(su), check_something(sa))
    print(su,sa)
    if check_something(su) == True:
        return plain_1
    
    if check_something(sa) == True:
        return plain_2
    
    
print(ind_cca2(G, ciph, plain_1, plain_2))


#########


###IND cca 2 for classic mceliece