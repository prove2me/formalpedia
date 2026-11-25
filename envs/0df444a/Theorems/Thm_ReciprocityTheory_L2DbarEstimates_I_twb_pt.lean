-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_twb_pt
-- name    : ReciprocityTheory.L2DbarEstimates.I.twb_pt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:06.761052+00:00
-- url     : https://prove2.me/theorems/c0ee267e-fb40-541f-a561-47747259361e
-- title:
--   I: twb pt
-- statement:
--   The I construction uses the twb pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwBound.lean#L108-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwBound.lean#L108-L130

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.twb_pt (p a b T : ℝ) (D0 DP u : ℂ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (h0 : ‖D0‖ ^ 2 ≤ a * T) (h1 : ‖DP‖ ^ 2 ≤ b * T) :
    ‖Complex.exp p * (D0 + u * DP)‖ ^ 2 ≤
      Real.exp (2 * p) * (Real.sqrt a + ‖u‖ * Real.sqrt b) ^ 2 * T := by sorry
