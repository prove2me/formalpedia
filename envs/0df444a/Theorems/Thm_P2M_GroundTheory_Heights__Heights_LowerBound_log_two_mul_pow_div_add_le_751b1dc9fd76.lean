-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_log_two_mul_pow_div_add_le_751b1dc9fd76
-- name    : P2M_GroundTheory_Heights__Heights_LowerBound_log_two_mul_pow_div_add_le_751b1dc9fd76
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:51.280508+00:00
-- url     : https://prove2.me/theorems/6619d3ba-18de-46a6-b8a6-3d3f2021d1b0
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound log two mul pow div add le 751b1dc9fd76: P2 M Ground Theory Heights  Heights Lower Bound log two mul pow div add le 751b1dc9fd76
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound log two mul pow div add le 751b1dc9fd76 construction uses the P2 M Ground Theory Heights  Heights Lower Bound log two mul pow div add le 751b1dc9fd76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PMeanLogPlus.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PMeanLogPlus.lean#L23-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMeanLogPlus
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
open Real MeasureTheory Filter Topology Set
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_LowerBound_log_two_mul_pow_div_add_le_751b1dc9fd76 {a : ℕ} {k : ℝ} (ha : 1 ≤ a) (hk : 3 * (a : ℝ) ≤ k) :
    log (2 * 36 ^ a) / k + 1 / k ≤ 3 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBound».«log_two_mul_pow_div_add_le» := P2M_GroundTheory_Heights__Heights_LowerBound_log_two_mul_pow_div_add_le_751b1dc9fd76
