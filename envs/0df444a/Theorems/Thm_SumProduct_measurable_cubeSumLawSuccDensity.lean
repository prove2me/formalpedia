-- Prove2me | Theorems.Thm_SumProduct_measurable_cubeSumLawSuccDensity
-- name    : SumProduct.measurable_cubeSumLawSuccDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:57:40.864789+00:00
-- url     : https://prove2.me/theorems/0f5a14cf-6d2e-4666-bd56-ad4d8da2af2d
-- title:
--   Sum Product: measurable cube Sum Law Succ Density
-- statement:
--   The Sum Product construction uses the measurable cube Sum Law Succ Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L243-L250
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L243-L250

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

theorem SumProduct.measurable_cubeSumLawSuccDensity (n : ℕ) :
    Measurable (cubeSumLawSuccDensity n) := by sorry
