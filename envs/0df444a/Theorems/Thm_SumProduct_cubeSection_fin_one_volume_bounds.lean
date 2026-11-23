-- Prove2me | Theorems.Thm_SumProduct_cubeSection_fin_one_volume_bounds
-- name    : SumProduct.cubeSection_fin_one_volume_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:57:01.018793+00:00
-- url     : https://prove2.me/theorems/5c078f0f-c424-4759-bc07-98e3eaefac63
-- title:
--   Sum Product: cube Section fin one volume bounds
-- statement:
--   The target two-sided bound for the unit cube section in dimension `n ≥ 1`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L573-L597
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L573-L597

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

theorem SumProduct.cubeSection_fin_one_volume_bounds (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ) ≤
        (volume (cubeSection (Fin n) 1)).toReal ∧
      (volume (cubeSection (Fin n) 1)).toReal ≤
        5 * (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ) := by sorry
