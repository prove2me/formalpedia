-- Prove2me | Theorems.Thm_SumProduct_integrable_cubeSumLawSuccDensity_toReal
-- name    : SumProduct.integrable_cubeSumLawSuccDensity_toReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:59:38.948033+00:00
-- url     : https://prove2.me/theorems/1e321916-e797-410e-bea9-344307102f92
-- title:
--   Sum Product: integrable cube Sum Law Succ Density to Real
-- statement:
--   The Sum Product construction uses the integrable cube Sum Law Succ Density to Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L265-L269
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L265-L269

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

theorem SumProduct.integrable_cubeSumLawSuccDensity_toReal (n : ℕ) :
    Integrable (fun x : ℝ => (cubeSumLawSuccDensity n x).toReal) := by sorry
