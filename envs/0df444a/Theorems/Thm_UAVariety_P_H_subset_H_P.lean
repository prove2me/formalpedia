-- Prove2me | Theorems.Thm_UAVariety_P_H_subset_H_P
-- name    : UAVariety.P_H_subset_H_P
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:39:38.662905+00:00
-- url     : https://prove2.me/theorems/23627562-b66c-4169-8246-18b5f5dfef63
-- title:
--   Lemma 9.2: PH ⊆ HP
-- statement:
--   $L$ is a signature without relation symbols; an algebra is a type in `Type u` with an $L$-structure (`Alg L`), and $K$ is an arbitrary class of algebras. $H(K)$ is the class of surjective homomorphic images of members of $K$; $S(K)$ is the class of algebras admitting an embedding into a member of $K$; $P(K)$ is the class of algebras isomorphic to a direct product (coordinatewise operations), indexed by an arbitrary, possibly empty, type in `Type u`, of members of $K$.
--
--   **Claim.** $P(H(K))\subseteq H(P(K))$: an algebra isomorphic to a product of homomorphic images of members of $K$ is a homomorphic image of a product of members of $K$ (coordinatewise surjection, using choice).
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Lemma 9.2

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Lemma 9.2: `PH ≤ HP`. A product of homomorphic images of members of `K` is a homomorphic image of a product of members of `K`. -/
theorem P_H_subset_H_P (K : Set (Alg L)) : P (H K) ⊆ H (P K) := by sorry

end UAVariety
