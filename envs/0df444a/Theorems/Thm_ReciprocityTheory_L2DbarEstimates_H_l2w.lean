-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_l2w
-- name    : ReciprocityTheory.L2DbarEstimates.H.l2w
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:44.067571+00:00
-- url     : https://prove2.me/theorems/59f91a2d-a435-4d54-bddb-57052ad8a250
-- title:
--   H: l2w
-- statement:
--   The H construction uses the l2w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/WeightedIntegralEqLintegral.lean#L36-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/WeightedIntegralEqLintegral.lean#L36-L52

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
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

theorem ReciprocityTheory.L2DbarEstimates.H.l2w (n : ℕ) (M : Type*) [MeasurableSpace M] : WeightedL2Properties n M := by sorry
