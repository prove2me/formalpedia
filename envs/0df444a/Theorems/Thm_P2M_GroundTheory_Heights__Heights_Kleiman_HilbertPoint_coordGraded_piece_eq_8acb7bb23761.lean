-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_coordGraded_piece_eq_8acb7bb23761
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_coordGraded_piece_eq_8acb7bb23761
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:53.744782+00:00
-- url     : https://prove2.me/theorems/b4e160eb-e514-48d5-a680-9f1b4be27f55
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point coord Graded piece eq 8acb7bb23761: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point coord Graded piece eq 8acb7bb23761
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point coord Graded piece eq 8acb7bb23761 construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point coord Graded piece eq 8acb7bb23761 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L160-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L160-L176

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_coordGraded_piece_eq_8acb7bb23761 (hj : y j ≠ 0) (n : ℕ) :
    (coordGraded k y).piece (n : ℤ) = (affPiece k y j n).map (LinearMap.mulLeft k (y j ^ n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«coordGraded_piece_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_coordGraded_piece_eq_8acb7bb23761
