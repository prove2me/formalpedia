-- Prove2me | Theorems.Thm_SumProduct_cubeSumLaw_measure_Icc_toReal_eq_integral_density
-- name    : SumProduct.cubeSumLaw_measure_Icc_toReal_eq_integral_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:55:26.101566+00:00
-- url     : https://prove2.me/theorems/0fa71e59-d82c-443b-9220-8936e6ea1c7e
-- title:
--   Sum Product: cube Sum Law measure Icc to Real eq integral density
-- statement:
--   The Sum Product construction uses the cube Sum Law measure Icc to Real eq integral density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L276-L290
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L276-L290

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

theorem SumProduct.cubeSumLaw_measure_Icc_toReal_eq_integral_density (m : ℕ) (a b : ℝ) :
    (cubeSumLaw (m + 1) (Set.Icc a b)).toReal =
      ∫ x in Set.Icc a b, (cubeSumLawSuccDensity m x).toReal := by sorry
