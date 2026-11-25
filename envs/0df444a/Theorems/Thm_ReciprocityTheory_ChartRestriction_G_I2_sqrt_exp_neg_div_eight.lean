-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sqrt_exp_neg_div_eight
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sqrt_exp_neg_div_eight
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:26.274054+00:00
-- url     : https://prove2.me/theorems/f6655037-b5ad-51af-8d81-5f63957b3d5c
-- title:
--   I2: sqrt exp neg div eight
-- statement:
--   The I2 construction uses the sqrt exp neg div eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean#L43-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory

theorem ReciprocityTheory.ChartRestriction.G.I2.sqrt_exp_neg_div_eight (x : ℝ) : Real.sqrt (Real.exp (-x / 8)) = Real.exp (-x / 16) := by sorry
