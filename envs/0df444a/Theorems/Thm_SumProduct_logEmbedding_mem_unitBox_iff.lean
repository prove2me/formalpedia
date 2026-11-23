-- Prove2me | Theorems.Thm_SumProduct_logEmbedding_mem_unitBox_iff
-- name    : SumProduct.logEmbedding_mem_unitBox_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:47:20.794146+00:00
-- url     : https://prove2.me/theorems/4e33ad5f-0d82-4068-999f-34d4fe8dc2d3
-- title:
--   Sum Product: log Embedding mem unit Box iff
-- statement:
--   For totally real `K`, a unit lies in `B^×(Y)` iff its log-embedding lies in `unitBox K Y`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L122-L146
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L122-L146

import Mathlib
import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  NumberField.InfinitePlace

theorem SumProduct.logEmbedding_mem_unitBox_iff {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} {u : (𝓞 K)ˣ} :
    logEmbedding K (Additive.ofMul u) ∈ unitBox K Y ↔ u ∈ boxMult K Y := by sorry
