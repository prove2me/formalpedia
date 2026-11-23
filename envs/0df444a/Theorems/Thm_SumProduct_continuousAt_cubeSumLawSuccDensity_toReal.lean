-- Prove2me | Theorems.Thm_SumProduct_continuousAt_cubeSumLawSuccDensity_toReal
-- name    : SumProduct.continuousAt_cubeSumLawSuccDensity_toReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:56:21.6528+00:00
-- url     : https://prove2.me/theorems/74422c53-6580-4f85-ad33-48460d2a5451
-- title:
--   Sum Product: continuous At cube Sum Law Succ Density to Real
-- statement:
--   The Sum Product construction uses the continuous At cube Sum Law Succ Density to Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L341-L364
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L341-L364

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

theorem SumProduct.continuousAt_cubeSumLawSuccDensity_toReal
    (n : ℕ) (hn : 1 ≤ n) :
    ContinuousAt (fun z : ℝ => (cubeSumLawSuccDensity n z).toReal) 0 := by sorry
