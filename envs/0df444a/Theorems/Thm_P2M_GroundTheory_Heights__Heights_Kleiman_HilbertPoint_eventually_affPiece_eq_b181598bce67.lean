-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_eventually_affPiece_eq_b181598bce67
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_eventually_affPiece_eq_b181598bce67
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:52.166717+00:00
-- url     : https://prove2.me/theorems/5d79216c-011c-4fa6-ba38-369af9b521c6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point eventually aff Piece eq b181598bce67: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point eventually aff Piece eq b181598bce67
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point eventually aff Piece eq b181598bce67 construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point eventually aff Piece eq b181598bce67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L142-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L142-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_eventually_affPiece_eq_b181598bce67 (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    ∀ᶠ n : ℕ in atTop, affPiece k y j n = Subalgebra.toSubmodule (affRing k y j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«eventually_affPiece_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_eventually_affPiece_eq_b181598bce67
