-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mollify_eq_convolution
-- name    : ReciprocityTheory.L2DbarEstimates.C.mollify_eq_convolution
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:55:29.246566+00:00
-- url     : https://prove2.me/theorems/bce33852-7f36-48a9-974c-f03439537c42
-- title:
--   C: mollify eq convolution
-- statement:
--   The C construction uses the mollify eq convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MollifyEqConvolution.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MollifyEqConvolution.lean#L9-L13

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralMollProfBall
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff Convolution

theorem ReciprocityTheory.L2DbarEstimates.C.mollify_eq_convolution (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = (moll n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by sorry
