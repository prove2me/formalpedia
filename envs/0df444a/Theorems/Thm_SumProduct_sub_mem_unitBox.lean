-- Prove2me | Theorems.Thm_SumProduct_sub_mem_unitBox
-- name    : SumProduct.sub_mem_unitBox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:56:07.582063+00:00
-- url     : https://prove2.me/theorems/f6846c27-61b3-4fd5-a590-d64c9adf4325
-- title:
--   Sum Product: sub mem unit Box
-- statement:
--   Differences of `unitBox` points add radii: `unitBox a − unitBox b ⊆ unitBox (a+b)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L151-L164
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L151-L164

import Mathlib
import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem SumProduct.sub_mem_unitBox {K : Type*} [Field K] [NumberField K] {y z : logSpace K} {a b : ℝ}
    (hy : y ∈ unitBox K a) (hz : z ∈ unitBox K b) : y - z ∈ unitBox K (a + b) := by sorry
