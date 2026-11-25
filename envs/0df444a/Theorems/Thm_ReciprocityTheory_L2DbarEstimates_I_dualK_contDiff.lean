-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualK_contDiff
-- name    : ReciprocityTheory.L2DbarEstimates.I.dualK_contDiff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:30.692218+00:00
-- url     : https://prove2.me/theorems/d23e6bbc-fc09-492f-8f8e-88c0b86dabef
-- title:
--   I: dual K cont Diff
-- statement:
--   The I construction uses the dual K cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/AddLogPosOfThreeQuartersLe.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/AddLogPosOfThreeQuartersLe.lean#L43-L51

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

theorem ReciprocityTheory.L2DbarEstimates.I.dualK_contDiff (c : ℝ) : ContDiff ℝ ∞ (dualK c) := by sorry
