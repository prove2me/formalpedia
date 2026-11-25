-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_hasDerivAt_kp
-- name    : ReciprocityTheory.L2DbarEstimates.I.tl_hasDerivAt_kp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:44.597594+00:00
-- url     : https://prove2.me/theorems/afab292a-321f-5694-9225-3a32aa593297
-- title:
--   I: tl has Deriv At kp
-- statement:
--   The I construction uses the tl has Deriv At kp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean#L80-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean#L80-L92

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

theorem ReciprocityTheory.L2DbarEstimates.I.tl_hasDerivAt_kp (c t : ℝ) (hs : 9 / 10 ≤ c - t) : HasDerivAt (tlKp c) (tlKpp c t) t := by sorry
