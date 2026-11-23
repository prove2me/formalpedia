-- Prove2me | Theorems.Thm_SumProduct_volume_cubeSection_one_congr
-- name    : SumProduct.volume_cubeSection_one_congr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:52:15.415824+00:00
-- url     : https://prove2.me/theorems/9961cd97-41e4-448f-a5e7-f7b0ddfdfd5b
-- title:
--   Sum Product: volume cube Section one congr
-- statement:
--   The unit cube-section volume depends only on `Fintype.card ι`: reindexing the coordinates by an
--   equivalence `Fin n ≃ ι` is measure-preserving and carries one box to the other. This lets the
--   analytic core be proved over `Fin n` and transported to `{w ≠ w₀}`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L134-L152
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L134-L152

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
open scoped Classical

theorem SumProduct.volume_cubeSection_one_congr (ι : Type*) [Fintype ι] :
    volume (cubeSection ι 1) = volume (cubeSection (Fin (Fintype.card ι)) 1) := by sorry
