-- Prove2me | Theorems.Thm_PCB_lex_cone_conj
-- name    : PCB.lex_cone_conj
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:08:40.590367+00:00
-- url     : https://prove2.me/theorems/2574d269-e72f-4148-adcf-450c9959feff
-- title:
--   The lexicographic cone is invariant under conjugation (Theorem 4 (iii))
-- statement:
--   The lexicographic cone is invariant under conjugation. Conjugation acts componentwise on the normal form through the cone-preserving action of the ambient group on each free factor, so the highest nontrivial component of a conjugate of a positive element is again positive. This is Theorem 4 (iii) of the paper, the ingredient that makes the lexicographic ordering bi-invariant.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Theorem 4 (iii)).

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB

/-!  Milestone 3 (Theorem 4 (iii)): the lexicographic cone is invariant
under conjugation. Conjugation acts componentwise through the
cone-preserving action on each free factor, and the almost-direct property
makes the action preserve the Magnus-type cone, so the highest nontrivial
component of a conjugate of a positive element is again positive. -/
theorem lex_cone_conj {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    ∀ g ∈ lexCone W, ∀ x : G, x * g * x⁻¹ ∈ lexCone W := by sorry

end PCB
