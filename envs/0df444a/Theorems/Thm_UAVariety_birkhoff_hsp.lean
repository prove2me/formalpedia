-- Prove2me | Theorems.Thm_UAVariety_birkhoff_hsp
-- name    : UAVariety.birkhoff_hsp
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T14:19:04.730727+00:00
-- url     : https://prove2.me/theorems/e613912a-5093-42b5-b03b-14258edf34f0
-- title:
--   Birkhoff's HSP theorem
-- statement:
--   $L$ is a signature without relation symbols; an algebra is a type in `Type u` with an $L$-structure (`Alg L`), and $K$ is a class of algebras. $H(K)$, $S(K)$, $P(K)$ are the classes of homomorphic images, of algebras embeddable in, and of algebras isomorphic to direct products (over any index type in `Type u`, possibly empty) of members of $K$; $K$ is a variety if it is closed under $H$, $S$ and $P$. $A\models p\approx q$ means $p$ and $q$ agree under every assignment of the variables in $A$; $\mathrm{Mod}(E)$ is the class of algebras satisfying every identity in $E$ (identities over the variables $\mathbb N$), and $\mathrm{Id}(K)$ the set of identities over $\mathbb N$ true in every member of $K$. A class $K$ of algebras is a variety if and only if $K=\mathrm{Mod}(\mathrm{Id}(K))$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Theorem 11.9 (Birkhoff) together with Lemma 11.8; G. Birkhoff, Proc. Cambridge Philos. Soc. 31 (1935) 433-454, https://doi.org/10.1017/S0305004100013463

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Birkhoff's HSP theorem (B&S Thm 11.9 with Lemma 11.8): a class of algebras is a
variety iff it is the class of models of its own identities over countably many variables. -/
theorem birkhoff_hsp (K : Set (Alg L)) : IsVariety K ↔ K = Mod (Id K) := by sorry

end UAVariety
