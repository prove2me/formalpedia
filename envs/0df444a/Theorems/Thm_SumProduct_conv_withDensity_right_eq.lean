-- Prove2me | Theorems.Thm_SumProduct_conv_withDensity_right_eq
-- name    : SumProduct.conv_withDensity_right_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:54:21.878008+00:00
-- url     : https://prove2.me/theorems/44730896-8a1a-4278-9292-5ddde3994850
-- title:
--   Sum Product: conv with Density right eq
-- statement:
--   The Sum Product construction uses the conv with Density right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L169-L205
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L169-L205

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

theorem SumProduct.conv_withDensity_right_eq
    (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    μ ∗ volume.withDensity f =
      volume.withDensity (fun z : ℝ => ∫⁻ x : ℝ, f (z - x) ∂μ) := by sorry
