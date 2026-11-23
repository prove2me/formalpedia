-- Prove2me | Theorems.Thm_SumProduct_cubeSumLawSuccDensity_toReal_eq_half_intervalIntegral
-- name    : SumProduct.cubeSumLawSuccDensity_toReal_eq_half_intervalIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:55:40.083051+00:00
-- url     : https://prove2.me/theorems/c7e13d71-1ffc-496e-aad8-2c1ff391be05
-- title:
--   Sum Product: cube Sum Law Succ Density to Real eq half interval Integral
-- statement:
--   The Sum Product construction uses the cube Sum Law Succ Density to Real eq half interval Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L321-L339
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L321-L339

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

theorem SumProduct.cubeSumLawSuccDensity_toReal_eq_half_intervalIntegral
    (n : ℕ) (hn : 1 ≤ n) (z : ℝ) :
    (cubeSumLawSuccDensity n z).toReal =
      (1 / 2 : ℝ) * ∫ x in (z - 1)..(z + 1),
        (cubeSumLawSuccDensity (n - 1) x).toReal := by sorry
