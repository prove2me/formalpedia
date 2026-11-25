-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_dop_div
-- name    : ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.dop_div
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:02.782639+00:00
-- url     : https://prove2.me/theorems/60b4d7a6-a512-5dae-898e-0cc883c8cde5
-- title:
--   Flat Weighted Estimates: dop div
-- statement:
--   The Flat Weighted Estimates construction uses the dop div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L75-L79

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
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
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates

theorem ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.dop_div {n : ℕ} (h : Fin n → V n → ℂ) (y : V n) :
    B.Dop (cD n) (vD n) (fun p => h (finProdFinEquiv.symm p).1) y = ∑ j, wd n j (h j) y := by sorry
