-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cutoff
-- name    : ReciprocityTheory.L2DbarEstimates.F.cutoff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:36.449807+00:00
-- url     : https://prove2.me/theorems/2c075ec0-372d-5bb5-880b-0ab84e692325
-- title:
--   F: cutoff
-- statement:
--   The F construction uses the cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Cutoff.lean#L106-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Cutoff.lean#L106-L283

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
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

theorem ReciprocityTheory.L2DbarEstimates.F.cutoff (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMA : MultAdjStatement n M) (hMS : MultSStatement n M) :
    CutoffStatement n M := by sorry
