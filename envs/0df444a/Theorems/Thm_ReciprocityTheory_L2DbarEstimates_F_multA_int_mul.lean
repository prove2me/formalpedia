-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_int_mul
-- name    : ReciprocityTheory.L2DbarEstimates.F.multA_int_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:18.403528+00:00
-- url     : https://prove2.me/theorems/479e70c6-2bf4-49a7-b49f-307491cf2893
-- title:
--   F: mult A int mul
-- statement:
--   The F construction uses the mult A int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L87-L94

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.multA_int_mul {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) (u c : M → ℂ)
    (hu : ∀ K, IsCompact K → IntegrableOn u K μ) (hc : Continuous c) (hcs : HasCompactSupport c) :
    Integrable (fun x => u x * c x) μ := by sorry
