-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_integrable_of_sq
-- name    : ReciprocityTheory.L2DbarEstimates.F.multA_integrable_of_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:20.999688+00:00
-- url     : https://prove2.me/theorems/60885283-8aca-46d6-ab6d-b2506bf62350
-- title:
--   F: mult A integrable of sq
-- statement:
--   The F construction uses the mult A integrable of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L11-L18

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

theorem ReciprocityTheory.L2DbarEstimates.F.multA_integrable_of_sq {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (F : α → ℂ) (hF : AEStronglyMeasurable F ν) (h : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ⊤) :
    Integrable F ν := by sorry
