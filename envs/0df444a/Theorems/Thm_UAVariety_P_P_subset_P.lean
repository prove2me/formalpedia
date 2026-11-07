-- Prove2me | Theorems.Thm_UAVariety_P_P_subset_P
-- name    : UAVariety.P_P_subset_P
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:39:41.199197+00:00
-- url     : https://prove2.me/theorems/4db2f33f-4091-40b0-8bb0-8ec805711077
-- title:
--   PP ⊆ P: products of products are products
-- statement:
--   $L$ is a signature without relation symbols; an algebra is a type in `Type u` with an $L$-structure (`Alg L`), and $K$ is an arbitrary class of algebras. $H(K)$ is the class of surjective homomorphic images of members of $K$; $S(K)$ is the class of algebras admitting an embedding into a member of $K$; $P(K)$ is the class of algebras isomorphic to a direct product (coordinatewise operations), indexed by an arbitrary, possibly empty, type in `Type u`, of members of $K$.
--
--   **Claim.** $P(P(K))\subseteq P(K)$: an algebra isomorphic to a product $\prod_i A_i$ with each $A_i\cong\prod_{j\in J_i}C_{ij}$, $C_{ij}\in K$, is isomorphic to the product $\prod_{(i,j)}C_{ij}$ over the dependent pair type $\Sigma_i J_i$ (which again lies in `Type u`).
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §9 (Lemma 9.2 / Theorem 9.5)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- `PP ≤ P` (B&S Ch. II §9): a product of products of members of `K` is (isomorphic to) a single product of members of `K`, indexed by the dependent pair type. -/
theorem P_P_subset_P (K : Set (Alg L)) : P (P K) ⊆ P K := by sorry

end UAVariety
