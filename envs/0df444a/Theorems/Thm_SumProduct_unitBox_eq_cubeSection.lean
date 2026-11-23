-- Prove2me | Theorems.Thm_SumProduct_unitBox_eq_cubeSection
-- name    : SumProduct.unitBox_eq_cubeSection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:51:30.567803+00:00
-- url     : https://prove2.me/theorems/1069dea6-3a22-4bc8-8d3a-3ba67d79a91a
-- title:
--   Sum Product: unit Box eq cube Section
-- statement:
--   `unitBox K r` is, on the nose, the sum-constrained cube over the index `{w ≠ w₀}` of
--   `logSpace K`. This is the (Jacobian-free) transport identity for the volume.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L54-L55
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L54-L55

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem SumProduct.unitBox_eq_cubeSection (K : Type*) [Field K] [NumberField K] (r : ℝ) :
    unitBox K r = cubeSection {w : InfinitePlace K // w ≠ w₀} r := by sorry
