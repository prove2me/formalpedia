-- Prove2me | Theorems.Thm_SumProduct_add_mem_unitBox
-- name    : SumProduct.add_mem_unitBox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:53.496779+00:00
-- url     : https://prove2.me/theorems/a4593183-9f71-458b-a5aa-449043a85ade
-- title:
--   Sum Product: add mem unit Box
-- statement:
--   Sums of `unitBox` points add radii: `unitBox a + unitBox b ⊆ unitBox (a+b)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L169-L179
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L169-L179

import Mathlib
import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem SumProduct.add_mem_unitBox {K : Type*} [Field K] [NumberField K] {y z : logSpace K} {a b : ℝ}
    (hy : y ∈ unitBox K a) (hz : z ∈ unitBox K b) : y + z ∈ unitBox K (a + b) := by sorry
