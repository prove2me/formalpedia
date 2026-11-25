-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_mul_le_sqrt_mul_sqrt_mul_avg
-- name    : ReciprocityTheory.ChartRestriction.G.I2.mul_le_sqrt_mul_sqrt_mul_avg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:14.046473+00:00
-- url     : https://prove2.me/theorems/5df90093-7243-5033-8c57-69e5aea4c5aa
-- title:
--   I2: mul le sqrt mul sqrt mul avg
-- statement:
--   The I2 construction uses the mul le sqrt mul sqrt mul avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean#L21-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean#L21-L41

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

theorem ReciprocityTheory.ChartRestriction.G.I2.mul_le_sqrt_mul_sqrt_mul_avg {u v A B P Q t : ℝ} (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t) (huP : u ^ 2 ≤ A * P) (hvQ : v ^ 2 ≤ B * Q) :
    u * v ≤ Real.sqrt A * Real.sqrt B * ((t * P + Q / t) / 2) := by sorry
