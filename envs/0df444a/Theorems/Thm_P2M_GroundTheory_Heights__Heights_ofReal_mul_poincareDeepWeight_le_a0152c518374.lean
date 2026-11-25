-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ofReal_mul_poincareDeepWeight_le_a0152c518374
-- name    : P2M_GroundTheory_Heights__Heights_ofReal_mul_poincareDeepWeight_le_a0152c518374
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:11.446719+00:00
-- url     : https://prove2.me/theorems/b5163116-bf5f-44b7-a1ba-096b6ead8370
-- title:
--   P2 M Ground Theory Heights  Heights of Real mul poincare Deep Weight le a0152c518374: P2 M Ground Theory Heights  Heights of Real mul poincare Deep Weight le a0152c518374
-- statement:
--   The P2 M Ground Theory Heights  Heights of Real mul poincare Deep Weight le a0152c518374 construction uses the P2 M Ground Theory Heights  Heights of Real mul poincare Deep Weight le a0152c518374 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepWeightMass.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepWeightMass.lean#L41-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepWeightMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ofReal_mul_poincareDeepWeight_le_a0152c518374 (r : ℝ) :
    ENNReal.ofReal r * ENNReal.ofReal (if Real.log (|r| ^ 2) < -Real.exp 1 then
        (|r| ^ 2 * Real.log (|r| ^ 2) ^ 2)⁻¹ else 0) ≤
      (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))).indicator
        (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ofReal_mul_poincareDeepWeight_le» := P2M_GroundTheory_Heights__Heights_ofReal_mul_poincareDeepWeight_le_a0152c518374
