-- Prove2me | Theorems.Thm_SumProduct_cubeSumLawSuccDensity_zero_toReal
-- name    : SumProduct.cubeSumLawSuccDensity_zero_toReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:54:48.544078+00:00
-- url     : https://prove2.me/theorems/dd8b9626-a808-4df2-b71e-de866d0360f7
-- title:
--   Sum Product: cube Sum Law Succ Density zero to Real
-- statement:
--   The Sum Product construction uses the cube Sum Law Succ Density zero to Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L236-L241
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L236-L241

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

theorem SumProduct.cubeSumLawSuccDensity_zero_toReal (n : ℕ) :
    (cubeSumLawSuccDensity n 0).toReal =
      (1 / 2 : ℝ) * (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal := by sorry
