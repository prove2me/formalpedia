-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlK_eventually
-- name    : ReciprocityTheory.L2DbarEstimates.I.tlK_eventually
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:38.037601+00:00
-- url     : https://prove2.me/theorems/23019360-c90f-4f6b-8f86-4f71ece5dd68
-- title:
--   I: tl K eventually
-- statement:
--   The I construction uses the tl K eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean#L61-L65

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
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
noncomputable section
open Filter Topology

theorem ReciprocityTheory.L2DbarEstimates.I.tlK_eventually (c t : ℝ) (ht : t < c - 19 / 20) :
    tlK c =ᶠ[𝓝 t] fun t => -Real.log ((c - t) + Real.log (c - t)) := by sorry
