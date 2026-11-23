-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_comp
-- name    : ReciprocityTheory.L2DbarEstimates.F.chT_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:34.358947+00:00
-- url     : https://prove2.me/theorems/d131dc9d-930e-4602-ac14-be74d654c6d5
-- title:
--   F: ch T comp
-- statement:
--   The F construction uses the ch T comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L107-L108

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.chT_comp {n : ℕ} {M : Type*} [MeasurableSpace M] (μ : Measure M) (G : M → V n)
    (hG : AEStronglyMeasurable G μ) (j : Fin n) : AEStronglyMeasurable (fun x => G x j) μ := by sorry
