-- Prove2me | Theorems.Thm_SumProduct_integrable_fourier_cubeSumLawSuccDensity
-- name    : SumProduct.integrable_fourier_cubeSumLawSuccDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:56:20.471395+00:00
-- url     : https://prove2.me/theorems/5e175a8a-6962-4774-8bbe-94d08afa791a
-- title:
--   Sum Product: integrable fourier cube Sum Law Succ Density
-- statement:
--   The Sum Product construction uses the integrable fourier cube Sum Law Succ Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L378-L397
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L378-L397

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

theorem SumProduct.integrable_fourier_cubeSumLawSuccDensity (n : ℕ) (hn : 1 ≤ n) :
    Integrable (𝓕 (fun x : ℝ => ((cubeSumLawSuccDensity n x).toReal : ℂ))) := by sorry
