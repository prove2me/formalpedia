-- Prove2me | Theorems.Thm_SumProduct_cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun
-- name    : SumProduct.cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:56:36.11386+00:00
-- url     : https://prove2.me/theorems/e6fd7d1d-dda1-4bef-9024-0996411a280a
-- title:
--   Sum Product: cube Sum Law Succ Density zero eq inv two pi integral re char Fun
-- statement:
--   Fourier inversion at zero for the explicit density of `cubeSumLaw (n+1)`.
--
--   This is the remaining Route A analytic statement: use `cubeSumLaw_succ_eq_withDensity`, show the
--   real density `x ↦ (cubeSumLawSuccDensity n x).toReal` is continuous at `0`, identify its Fourier
--   transform with `charFun (cubeSumLaw (n+1))` under the `-2π` scaling, and apply
--   `MeasureTheory.Integrable.fourierInv_fourier_eq`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L406-L450
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L406-L450

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section

theorem SumProduct.cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun
    (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLawSuccDensity n 0).toReal =
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by sorry
