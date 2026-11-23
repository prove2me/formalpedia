-- Prove2me | Theorems.Thm_SumProduct_cubeSumLaw_Icc_eq_inv_pi_integral_re_charFun_succ
-- name    : SumProduct.cubeSumLaw_Icc_eq_inv_pi_integral_re_charFun_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:56:23.912474+00:00
-- url     : https://prove2.me/theorems/ffe7e8ef-755c-448a-9e57-801e81e04dfd
-- title:
--   Sum Product: cube Sum Law Icc eq inv pi integral re char Fun succ
-- statement:
--   Route A bridge, in the form needed for the cube law.
--
--   For `n ≥ 1`, add one independent uniform variable.  The law `cubeSumLaw (n + 1)` is then the
--   convolution of `cubeSumLaw n` with the uniform law on `[-1,1]`; its continuous density at `0` is
--   `(1 / 2) * cubeSumLaw n ([-1,1])`.  Fourier inversion at `0`, applied to this absolutely
--   continuous law whose characteristic function is integrable, gives the stated identity.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L459-L472
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L459-L472

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

theorem SumProduct.cubeSumLaw_Icc_eq_inv_pi_integral_re_charFun_succ (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by sorry
