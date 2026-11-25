-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualK_deriv
-- name    : ReciprocityTheory.L2DbarEstimates.I.dualK_deriv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:56:43.33801+00:00
-- url     : https://prove2.me/theorems/6f9b7ec6-51a2-40bd-b97e-08797e02aa9c
-- title:
--   I: dual K deriv
-- statement:
--   The I construction uses the dual K deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/AddLogPosOfThreeQuartersLe.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/AddLogPosOfThreeQuartersLe.lean#L58-L75

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
universe u
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.dualK_deriv {c t : ℝ} (h : 1 ≤ c - t) :
    deriv (dualK c) t = (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t)) := by sorry
