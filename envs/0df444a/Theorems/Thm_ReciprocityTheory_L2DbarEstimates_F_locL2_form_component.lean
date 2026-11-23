-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_form_component
-- name    : ReciprocityTheory.L2DbarEstimates.F.locL2_form_component
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:45.032822+00:00
-- url     : https://prove2.me/theorems/072cb279-1913-4dc0-aca6-19b9f6a7bbfd
-- title:
--   F: loc L2 form component
-- statement:
--   The F construction uses the loc L2 form component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L38-L45

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

theorem ReciprocityTheory.L2DbarEstimates.F.locL2_form_component {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) (f : M → V n) (hf : LocalL2Isometry μ f) (j : Fin n) :
    LocalL2Isometry μ (fun x => f x j) := by sorry
