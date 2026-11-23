-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_measurable_exp_neg_density
-- name    : ReciprocityTheory.L2DbarEstimates.H.measurable_exp_neg_density
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:37.009783+00:00
-- url     : https://prove2.me/theorems/37450fa5-c5f2-4438-959a-082523a79dc8
-- title:
--   H: measurable exp neg density
-- statement:
--   The H construction uses the measurable exp neg density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/WeightedIntegralEqLintegral.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/WeightedIntegralEqLintegral.lean#L8-L9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

theorem ReciprocityTheory.L2DbarEstimates.H.measurable_exp_neg_density {M : Type*} [MeasurableSpace M] {ψ : M → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (-ψ x))) := by sorry
