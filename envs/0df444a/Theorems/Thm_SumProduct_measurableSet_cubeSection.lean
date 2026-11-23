-- Prove2me | Theorems.Thm_SumProduct_measurableSet_cubeSection
-- name    : SumProduct.measurableSet_cubeSection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:51:46.322795+00:00
-- url     : https://prove2.me/theorems/9882e241-7ca2-4e84-a71a-20691d678922
-- title:
--   Sum Product: measurable Set cube Section
-- statement:
--   The Sum Product construction uses the measurable Set cube Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L47-L48
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L47-L48

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]

theorem SumProduct.measurableSet_cubeSection (r : ℝ) : MeasurableSet (cubeSection ι r) := by sorry
