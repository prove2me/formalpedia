-- Prove2me | Theorems.Thm_SumProduct_cubeSumLawSuccDensity_eq_half_measure_Icc
-- name    : SumProduct.cubeSumLawSuccDensity_eq_half_measure_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:55:39.317818+00:00
-- url     : https://prove2.me/theorems/ebdf65f6-8c38-4155-a5e0-e09243d517b1
-- title:
--   Sum Product: cube Sum Law Succ Density eq half measure Icc
-- statement:
--   The Sum Product construction uses the cube Sum Law Succ Density eq half measure Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L292-L312
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L292-L312

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

theorem SumProduct.cubeSumLawSuccDensity_eq_half_measure_Icc (n : ℕ) (z : ℝ) :
    cubeSumLawSuccDensity n z =
      (2 : ℝ≥0∞)⁻¹ * cubeSumLaw n (Set.Icc (z - 1) (z + 1)) := by sorry
