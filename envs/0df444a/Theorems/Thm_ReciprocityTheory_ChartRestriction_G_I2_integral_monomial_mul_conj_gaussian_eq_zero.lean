-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_monomial_mul_conj_gaussian_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.I2.integral_monomial_mul_conj_gaussian_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:36.312857+00:00
-- url     : https://prove2.me/theorems/e0cd234c-2851-5080-9ce6-0f036dd5cd6a
-- title:
--   I2: integral monomial mul conj gaussian eq zero
-- statement:
--   The I2 construction uses the integral monomial mul conj gaussian eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L140-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L140-L171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
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

theorem ReciprocityTheory.ChartRestriction.G.I2.integral_monomial_mul_conj_gaussian_eq_zero {g : ℕ} {α β : Fin g →₀ ℕ} (h : α ≠ β) :
    ∫ z : EuclideanSpace ℂ (Fin g),
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) = 0 := by sorry
