-- Prove2me | Theorems.Thm_UAVariety_S_H_subset_H_S
-- name    : UAVariety.S_H_subset_H_S
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:39:37.385282+00:00
-- url     : https://prove2.me/theorems/4ac861a8-23b5-4ea6-93dc-520e7cc26943
-- title:
--   Lemma 9.2: SH ⊆ HS
-- statement:
--   $L$ is a signature without relation symbols; an algebra is a type in `Type u` with an $L$-structure (`Alg L`), and $K$ is an arbitrary class of algebras. $H(K)$ is the class of surjective homomorphic images of members of $K$; $S(K)$ is the class of algebras admitting an embedding into a member of $K$; $P(K)$ is the class of algebras isomorphic to a direct product (coordinatewise operations), indexed by an arbitrary, possibly empty, type in `Type u`, of members of $K$.
--
--   **Claim.** $S(H(K))\subseteq H(S(K))$: every algebra embeddable in a homomorphic image of a member of $K$ is a homomorphic image of an algebra embeddable in a member of $K$. (Proof idea: pull the subalgebra back along the surjection.)
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Lemma 9.2

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Lemma 9.2: `SH ≤ HS`. A subalgebra of a homomorphic image of a member of `K` is a homomorphic image of a subalgebra of a member of `K`. -/
theorem S_H_subset_H_S (K : Set (Alg L)) : S (H K) ⊆ H (S K) := by sorry

end UAVariety
