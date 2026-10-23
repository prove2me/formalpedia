-- Prove2me | Theorems.Thm_PCB_lex_cone_mul
-- name    : PCB.lex_cone_mul
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:07:31.964677+00:00
-- url     : https://prove2.me/theorems/09f7ab03-01ea-4127-96b9-14314fd840e5
-- title:
--   The lexicographic cone is closed under multiplication (Theorem 4 (i))
-- statement:
--   The lexicographic cone of Definition 2 is closed under multiplication. If two elements have positive highest nontrivial normal-form components, then the highest of the two dominating indices controls the product, and at that index the Magnus-type positive cone of the corresponding free factor is closed under products, so the product again has positive highest nontrivial component. This is Theorem 4 (i) of the paper.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Theorem 4 (i)).

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB

/-!  Milestone 1 (Theorem 4 (i)): the lexicographic cone is closed under
multiplication. The product of two elements whose highest nontrivial
components are positive again has positive highest nontrivial component:
the highest of the two indices dominates, and the positive cones of the
free factors are closed under products. -/
theorem lex_cone_mul {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    ∀ a ∈ lexCone W, ∀ b ∈ lexCone W, a * b ∈ lexCone W := by sorry

end PCB
