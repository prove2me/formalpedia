-- Prove2me | Theorems.Thm_UAVariety_free_mem_SP
-- name    : UAVariety.free_mem_SP
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T14:18:40.833051+00:00
-- url     : https://prove2.me/theorems/ec22f4db-f528-4986-904d-7fd99a6e6295
-- title:
--   The free algebra lies in SP(K)
-- statement:
--   $L$ is a signature without relation symbols; an algebra is a type in `Type u` with an $L$-structure (`Alg L`), and $K$ is a class of algebras. $H(K)$, $S(K)$, $P(K)$ are the classes of homomorphic images, of algebras embeddable in, and of algebras isomorphic to direct products (over any index type in `Type u`, possibly empty) of members of $K$; $K$ is a variety if it is closed under $H$, $S$ and $P$. $F_K(\bar X)=T(X)/\theta_K(X)$, where $T(X)$ is the term algebra over $X$ and $\theta_K(X)$ is the intersection of all congruences $\varphi$ on $T(X)$ with $T(X)/\varphi\in S(K)$; $\bar x$ and $\bar p$ are the classes of a variable and of a term. For every type $X$ in `Type u`, $F_K(\bar X)\in S(P(K))$; consequently, if $K$ is closed under $S$ and $P$ (in particular if $K$ is a variety), then $F_K(\bar X)\in K$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Theorem 10.12 (Birkhoff)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Thm 10.12 (Birkhoff): `F_K(X̄) ∈ ISP(K)`; hence `F_K(X̄) ∈ K` whenever `K` is closed
under `S` and `P` (in particular when `K` is a variety). -/
theorem free_mem_SP (K : Set (Alg L)) (X : Type u) :
    freeAlg K X ∈ S (P K) ∧ (S K ⊆ K → P K ⊆ K → freeAlg K X ∈ K) := by sorry

end UAVariety
