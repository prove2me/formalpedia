-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unwBack_lint2
-- name    : ReciprocityTheory.L2DbarEstimates.F.unwBack_lint2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:18.332676+00:00
-- url     : https://prove2.me/theorems/e8483bb4-765b-49c8-8852-a8aab2d79b12
-- title:
--   F: unw Back lint2
-- statement:
--   The F construction uses the unw Back lint2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L62-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L62-L73

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

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

theorem ReciprocityTheory.L2DbarEstimates.F.unwBack_lint2 {M : Type*} [MeasurableSpace M] (μ : Measure M) (F A B : M → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hBm : AEMeasurable (fun x => ENNReal.ofReal (B x)) μ) (h : ∀ x, F x ≤ C * (A x + B x)) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal C *
      (∫⁻ x, ENNReal.ofReal (A x) ∂μ + ∫⁻ x, ENNReal.ofReal (B x) ∂μ) := by sorry
