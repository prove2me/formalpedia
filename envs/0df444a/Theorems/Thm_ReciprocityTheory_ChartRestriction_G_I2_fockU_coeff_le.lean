-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fockU_coeff_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.fockU_coeff_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:18.774699+00:00
-- url     : https://prove2.me/theorems/7d98778d-a08f-5295-9af6-1d6b17e42c2c
-- title:
--   I2: fock U coeff le
-- statement:
--   The I2 construction uses the fock U coeff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean#L103-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean#L103-L283

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

theorem ReciprocityTheory.ChartRestriction.G.I2.fockU_coeff_le {g c : ℕ} (a : EuclideanSpace ℂ (Fin g)) (F G : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : IsPolyLE c F) (hG : IsPolyLE c G) :
    ‖fockIP (fockU a F) G‖ ≤ 2 ^ (1 + 3 * ((g : ℝ) + c) / 2) * Real.exp (-‖a‖ ^ 2 / 16) *
      Real.sqrt (fockIP F F).re * Real.sqrt (fockIP G G).re := by sorry
