-- Prove2me | Theorems.Thm_SumProduct_cubeSumLawSuccDensity_toReal_eq_half_measure_Icc
-- name    : SumProduct.cubeSumLawSuccDensity_toReal_eq_half_measure_Icc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:55:30.032798+00:00
-- url     : https://prove2.me/theorems/cd08769c-5983-40db-9350-36aab741d93b
-- title:
--   Sum Product: cube Sum Law Succ Density to Real eq half measure Icc
-- statement:
--   The Sum Product construction uses the cube Sum Law Succ Density to Real eq half measure Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L314-L319
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L314-L319

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

theorem SumProduct.cubeSumLawSuccDensity_toReal_eq_half_measure_Icc (n : ℕ) (z : ℝ) :
    (cubeSumLawSuccDensity n z).toReal =
      (1 / 2 : ℝ) * (cubeSumLaw n (Set.Icc (z - 1) (z + 1))).toReal := by sorry
