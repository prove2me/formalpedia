-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_half_log_sub_le_d0d8b9aa61fb
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_half_log_sub_le_d0d8b9aa61fb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:37.739429+00:00
-- url     : https://prove2.me/theorems/75740c2d-8779-4fc0-8a96-98b2a5a9fa24
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff abs half log sub le d0d8b9aa61fb: P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff abs half log sub le d0d8b9aa61fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff abs half log sub le d0d8b9aa61fb construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff abs half log sub le d0d8b9aa61fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L16-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightDiffLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_half_log_sub_le_d0d8b9aa61fb {a ε κ : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hκ : 0 < κ) :
    |Real.log (a + ε * κ ^ 2) / 2 - Real.log (a + ε) / 2| ≤ |Real.log κ| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightDiff».«abs_half_log_sub_le» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_half_log_sub_le_d0d8b9aa61fb
