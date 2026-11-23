-- Prove2me | Theorems.Thm_SumProduct_charFun_uniformIntervalMeasure
-- name    : SumProduct.charFun_uniformIntervalMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:59:23.243644+00:00
-- url     : https://prove2.me/theorems/96c7da77-5dd3-4611-83c7-4de0e2edaeeb
-- title:
--   Sum Product: char Fun uniform Interval Measure
-- statement:
--   Characteristic function of the one-dimensional uniform law on `[-1, 1]`.
--
--   This is the elementary calculation
--   `(1 / 2) * ∫ x in [-1,1], exp (t * x * I) = sinc t`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L100-L119
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L100-L119

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

theorem SumProduct.charFun_uniformIntervalMeasure (t : ℝ) :
    charFun uniformIntervalMeasure t = (Real.sinc t : ℂ) := by sorry
