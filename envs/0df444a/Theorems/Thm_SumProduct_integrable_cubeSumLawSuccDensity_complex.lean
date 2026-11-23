-- Prove2me | Theorems.Thm_SumProduct_integrable_cubeSumLawSuccDensity_complex
-- name    : SumProduct.integrable_cubeSumLawSuccDensity_complex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:55:03.169823+00:00
-- url     : https://prove2.me/theorems/0ab36138-237d-4fe2-9147-30ff03c2d5fe
-- title:
--   Sum Product: integrable cube Sum Law Succ Density complex
-- statement:
--   The Sum Product construction uses the integrable cube Sum Law Succ Density complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L271-L274
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L271-L274

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

theorem SumProduct.integrable_cubeSumLawSuccDensity_complex (n : ℕ) :
    Integrable (fun x : ℝ => ((cubeSumLawSuccDensity n x).toReal : ℂ)) := by sorry
