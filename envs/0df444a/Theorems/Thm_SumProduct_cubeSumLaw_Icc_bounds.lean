-- Prove2me | Theorems.Thm_SumProduct_cubeSumLaw_Icc_bounds
-- name    : SumProduct.cubeSumLaw_Icc_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:56:53.33139+00:00
-- url     : https://prove2.me/theorems/219faa6f-7a95-4d2a-9bc1-7815e7d36ae1
-- title:
--   Sum Product: cube Sum Law Icc bounds
-- statement:
--   The remaining one-dimensional analytic estimate for the sum of independent uniforms on
--   `[-1,1]`.  This is the intended endpoint for either a B-spline/convolution proof or a Fourier proof.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L542-L570
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L542-L570

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

theorem SumProduct.cubeSumLaw_Icc_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.sqrt (n + 1 : ℝ) ≤ (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal ∧
      (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal ≤
        5 / Real.sqrt (n + 1 : ℝ) := by sorry
