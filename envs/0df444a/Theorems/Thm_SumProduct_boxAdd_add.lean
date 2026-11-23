-- Prove2me | Theorems.Thm_SumProduct_boxAdd_add
-- name    : SumProduct.boxAdd_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:37.331419+00:00
-- url     : https://prove2.me/theorems/189f0392-e80b-4d47-94f6-ce65d017a22f
-- title:
--   Sum Product: box Add add
-- statement:
--   Additive boxes add: `B⁺(X) + B⁺(Y) ⊆ B⁺(X+Y)` (the triangle inequality for places).
--   Used for the sumset bound `A + A ⊆ B⁺(4Xe^Y)` in Lemma 4.1.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L85-L91
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L85-L91

import Mathlib
import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct

theorem SumProduct.boxAdd_add {K : Type*} [Field K] [NumberField K] {X Y : ℝ} {α β : 𝓞 K}
    (ha : α ∈ boxAdd K X) (hb : β ∈ boxAdd K Y) : α + β ∈ boxAdd K (X + Y) := by sorry
