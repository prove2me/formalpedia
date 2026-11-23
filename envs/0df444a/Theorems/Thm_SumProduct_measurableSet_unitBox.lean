-- Prove2me | Theorems.Thm_SumProduct_measurableSet_unitBox
-- name    : SumProduct.measurableSet_unitBox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:23:06.859883+00:00
-- url     : https://prove2.me/theorems/9d8453ab-403f-4361-bd91-853e32d0bc20
-- title:
--   Sum Product: measurable Set unit Box
-- statement:
--   `unitBox K r` is measurable (it is closed).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L184-L192
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L184-L192

import Mathlib
import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem SumProduct.measurableSet_unitBox {K : Type*} [Field K] [NumberField K] (r : ℝ) :
    MeasurableSet (unitBox K r) := by sorry
