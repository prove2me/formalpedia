-- Prove2me | Theorems.Thm_SumProduct_uniformIntervalMeasure_eq_withDensity
-- name    : SumProduct.uniformIntervalMeasure_eq_withDensity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:54:25.831807+00:00
-- url     : https://prove2.me/theorems/daccb57a-a2b4-41a8-963f-c0d5094c6c46
-- title:
--   Sum Product: uniform Interval Measure eq with Density
-- statement:
--   The Sum Product construction uses the uniform Interval Measure eq with Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L146-L167
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L146-L167

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

theorem SumProduct.uniformIntervalMeasure_eq_withDensity :
    uniformIntervalMeasure =
      volume.withDensity
        (fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) x) := by sorry
