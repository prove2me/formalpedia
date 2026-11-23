-- Prove2me | Theorems.Thm_SumProduct_isClosed_cubeSection
-- name    : SumProduct.isClosed_cubeSection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:51:24.723797+00:00
-- url     : https://prove2.me/theorems/9aafe84f-ca41-4ce4-844e-e4fc6ca57fb8
-- title:
--   Sum Product: is Closed cube Section
-- statement:
--   The Sum Product construction uses the is Closed cube Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L40-L45
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L40-L45

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]

theorem SumProduct.isClosed_cubeSection (r : ℝ) : IsClosed (cubeSection ι r) := by sorry
