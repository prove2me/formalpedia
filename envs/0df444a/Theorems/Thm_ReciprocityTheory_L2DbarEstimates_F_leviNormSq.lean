-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_leviNormSq
-- name    : ReciprocityTheory.L2DbarEstimates.F.leviNormSq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:41.758201+00:00
-- url     : https://prove2.me/theorems/eb9298d5-3b6f-5ca6-b6c5-6ad16f988552
-- title:
--   F: levi Norm Sq
-- statement:
--   The F construction uses the levi Norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LeviZCoordChart.lean#L115-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LeviZCoordChart.lean#L115-L165

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LeviZCoordChart
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

theorem ReciprocityTheory.L2DbarEstimates.F.leviNormSq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LeviNormSqStatement n M := by sorry
