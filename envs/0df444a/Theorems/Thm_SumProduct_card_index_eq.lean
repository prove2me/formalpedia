-- Prove2me | Theorems.Thm_SumProduct_card_index_eq
-- name    : SumProduct.card_index_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:51:48.887939+00:00
-- url     : https://prove2.me/theorems/717f0241-b280-4aae-9691-2663431642cd
-- title:
--   Sum Product: card index eq
-- statement:
--   For a totally real field of degree `d`, the index type of `logSpace K` (i.e. `{w ≠ w₀}`) has
--   cardinality `d - 1`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L62-L72
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L62-L72

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
open scoped Classical
open NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem

theorem SumProduct.card_index_eq {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) :
    Fintype.card {w : InfinitePlace K // w ≠ w₀} = d - 1 := by sorry
