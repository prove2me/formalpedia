-- Prove2me | Theorems.Thm_SumProduct_boxMult_mul
-- name    : SumProduct.boxMult_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:45.998738+00:00
-- url     : https://prove2.me/theorems/c0a40bae-12db-4107-8dd3-3efccb56eadc
-- title:
--   Sum Product: box Mult mul
-- statement:
--   Multiplicative boxes multiply: `B^×(Y) · B^×(Y') ⊆ B^×(Y+Y')` (logarithms add).
--   Used for the small-doubling bound `G·G ⊆ B^×(2Y)` in Lemma 4.1.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L95-L107
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L95-L107

import Mathlib
import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct

theorem SumProduct.boxMult_mul {K : Type*} [Field K] [NumberField K] {Y Y' : ℝ} {u v : (𝓞 K)ˣ}
    (hu : u ∈ boxMult K Y) (hv : v ∈ boxMult K Y') : u * v ∈ boxMult K (Y + Y') := by sorry
