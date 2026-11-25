-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous_real
-- name    : ReciprocityTheory.L2DbarEstimates.integrable_of_continuous_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:19.784427+00:00
-- url     : https://prove2.me/theorems/beec8dd0-eb89-418c-b98c-0f8b5053df5d
-- title:
--   L2 Dbar Estimates: integrable of continuous real
-- statement:
--   The L2 Dbar Estimates construction uses the integrable of continuous real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L53-L57

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.integrable_of_continuous_real {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (vol n z) := by sorry
