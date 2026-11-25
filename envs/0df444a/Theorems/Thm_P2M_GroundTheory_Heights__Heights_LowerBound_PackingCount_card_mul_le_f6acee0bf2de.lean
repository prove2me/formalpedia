-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_PackingCount_card_mul_le_f6acee0bf2de
-- name    : P2M_GroundTheory_Heights__Heights_LowerBound_PackingCount_card_mul_le_f6acee0bf2de
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:43.627033+00:00
-- url     : https://prove2.me/theorems/b50ba900-2c7b-4283-9ea4-a6bc9ac5bf54
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Packing Count card mul le f6acee0bf2de: P2 M Ground Theory Heights  Heights Lower Bound Packing Count card mul le f6acee0bf2de
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Packing Count card mul le f6acee0bf2de construction uses the P2 M Ground Theory Heights  Heights Lower Bound Packing Count card mul le f6acee0bf2de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PPackingCount.lean#L11-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PPackingCount.lean#L11-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PPackingCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open MeasureTheory Metric
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LowerBound_PackingCount_card_mul_le_f6acee0bf2de {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) {lam R : ℝ} (hlam : 0 < lam) (hR : 0 ≤ R)
    (hT : ∀ x ∈ T, ‖x‖ < R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lam ≤ ‖x - y‖) :
    (T.card : ℝ) * (lam / 2) ^ Module.finrank ℝ E ≤ (R + lam / 2) ^ Module.finrank ℝ E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBound».«PackingCount».«card_mul_le» := P2M_GroundTheory_Heights__Heights_LowerBound_PackingCount_card_mul_le_f6acee0bf2de
