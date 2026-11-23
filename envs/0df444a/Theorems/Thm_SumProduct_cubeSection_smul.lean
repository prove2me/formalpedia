-- Prove2me | Theorems.Thm_SumProduct_cubeSection_smul
-- name    : SumProduct.cubeSection_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:51:39.654404+00:00
-- url     : https://prove2.me/theorems/0e58fe9b-5fbe-40f5-809a-40677e44f2a9
-- title:
--   Sum Product: cube Section smul
-- statement:
--   Homogeneity of the box: `cubeSection ι r = r • cubeSection ι 1` for `r ≥ 0`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L75-L105
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L75-L105

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]

theorem SumProduct.cubeSection_smul (r : ℝ) (hr : 0 ≤ r) :
    cubeSection ι r = r • cubeSection ι 1 := by sorry
