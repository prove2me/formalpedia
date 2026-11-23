-- Prove2me | Theorems.Thm_SumProduct_cubeSumLaw_Icc_eq_inv_pi_integral_sinc_mul_re_charFun
-- name    : SumProduct.cubeSumLaw_Icc_eq_inv_pi_integral_sinc_mul_re_charFun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:56:33.614951+00:00
-- url     : https://prove2.me/theorems/9140264f-2fed-46a9-96b0-f082fef77986
-- title:
--   Sum Product: cube Sum Law Icc eq inv pi integral sinc mul re char Fun
-- statement:
--   Route B analytic input: Fourier inversion of the interval indicator, integrated against the
--   sum law.
--
--   This is the missing Mathlib-facing fact behind the Parseval bridge.  It should follow from
--   `1_{[-1,1]}(x) = π⁻¹ ∫ t, sinc t * cos (t * x)` away from the two boundary points, plus Fubini and
--   `∫ cos (t*x) ∂μ = Re (charFun μ t)`.  The hypothesis `1 ≤ n` is used analytically to remove atoms
--   at `±1` and to get the integrability needed for Fubini.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L482-L499
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L482-L499

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

theorem SumProduct.cubeSumLaw_Icc_eq_inv_pi_integral_sinc_mul_re_charFun (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (Real.pi)⁻¹ * ∫ t : ℝ, Real.sinc t * (charFun (cubeSumLaw n) t).re := by sorry
