
// Define the group D4. B contains its elements (basis for Z[D4])
D4<sigma,rho> := sub<Sym(4)|(1,3),(1,2,3,4)>;
B := [rho^0,rho,rho^2,rho^3,sigma,rho*sigma,sigma*rho^2,sigma*rho];

// Construct the regular representation Z[D4] 
S8 := Sym(8);

// For each g in D4, define the permutation of B by b->bg
D4_regular_permrep := hom<D4->S8| g:->[Index(B,b*g): b in B]>; 
D4_in_S8 := Image(D4_regular_permrep);
regular_perm := hom<D4->D4_in_S8| [D4_regular_permrep(g): g in OrderedGenerators(D4)]>;
M8 := PermutationModule(D4_in_S8,Integers());

// sigma and rho become 8x8 matrices 
smat := Matrix(8,8,Eltseq(GModuleAction(M8)(regular_perm(sigma))));
rmat := Matrix(8,8,Eltseq(GModuleAction(M8)(regular_perm(rho))));
print "right-regular-representation of sigma",smat;
print "right-regular_representation of rho",rmat;
// if v in Z[D4], v.sigma is represented by v*smat and so on.

// Coordinate version of Z[D4]
Z8 := RSpace(Integers(),8);

one,r,r2,r3,s,rs,sr2,sr:=Explode(Basis(Z8));
idmat := smat^0;

// Represent the various maps by group ring elements 
phi := idmat+smat;
psi := idmat+rmat*smat;
phi := idmat+smat+rmat^2+rmat^2*smat;
phi_prime := idmat+rmat*smat+rmat^2+smat*rmat;

// Establish that P = Ker(phi_*) is ker(varphi_Phi) meet Image(Phi)
P := Kernel(phi) meet Image(phi);
print "space corresponding to prym P",P;

// Up to this point, everything is modeling what we have for the lemma. 

// We verify the basis for the space. Note that the magma code is for row-vectors
// and right action, whereas the paper is for left action and column vectors.
// that matters for rho*sigma vs. sigma*rho, so those signs are swapped.
// it doesn't matter, though, because all the statements are just concerning whatever P
// happens to be (so the precise ordering of the basis for the regular representation
// doesn't matter. It's just what the relations are.
P eq sub<Z8 | one+s-r2-sr2,r-sr+rs-r3>;

Pdual := Kernel(phi_prime) meet Image(psi);
print "space corresponding to prym Pdual",Pdual;

// we check that psi maps P into Pdual
// (This was also proven using the group theory in the thesis.)
P*psi subset Pdual;

// and we check that psi*phi (acting on the right) acts as multiplication-by-two
[b*psi*phi eq 2*b : b in Basis(P)];
