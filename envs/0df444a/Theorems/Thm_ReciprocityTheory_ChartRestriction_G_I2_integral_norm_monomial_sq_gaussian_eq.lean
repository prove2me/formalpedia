-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_norm_monomial_sq_gaussian_eq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.integral_norm_monomial_sq_gaussian_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:25.632802+00:00
-- url     : https://prove2.me/theorems/02cab734-829a-4b47-91a9-c53e0c433891
-- title:
--   I2: integral norm monomial sq gaussian eq
-- statement:
--   The I2 construction uses the integral norm monomial sq gaussian eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L13-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
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

theorem ReciprocityTheory.ChartRestriction.G.I2.integral_norm_monomial_sq_gaussian_eq {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.pi ^ g * fa1M α := by sorry
