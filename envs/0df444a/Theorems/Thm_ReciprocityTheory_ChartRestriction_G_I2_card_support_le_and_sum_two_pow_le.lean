-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_card_support_le_and_sum_two_pow_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.card_support_le_and_sum_two_pow_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:16.74751+00:00
-- url     : https://prove2.me/theorems/7ec39263-3c93-5169-9a13-172e87eccfa7
-- title:
--   I2: card support le and sum two pow le
-- statement:
--   The I2 construction uses the card support le and sum two pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean#L52-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean#L52-L101

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

theorem ReciprocityTheory.ChartRestriction.G.I2.card_support_le_and_sum_two_pow_le {g c : ℕ} (p : MvPolynomial (Fin g) ℂ) (hp : p.totalDegree ≤ c) :
    (p.support.card : ℝ) ≤ 2 ^ (g + c) ∧
      ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) ≤ 2 ^ (g + c) * 2 ^ (g + c) := by sorry
