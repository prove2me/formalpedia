-- Prove2me | Theorems.Thm_SumProduct_mem_boxMult
-- name    : SumProduct.mem_boxMult
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:47:22.441947+00:00
-- url     : https://prove2.me/theorems/d429bf44-bd56-42fd-844b-c676f26f4904
-- title:
--   Sum Product: mem box Mult
-- statement:
--   The Sum Product construction uses the mem box Mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L79-L81
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean#L79-L81

import Mathlib
import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct

theorem SumProduct.mem_boxMult {K : Type*} [Field K] [NumberField K] {Y : ℝ} {u : (𝓞 K)ˣ} :
    u ∈ boxMult K Y ↔ ∀ w : NumberField.InfinitePlace K, |Real.log (w ((u : 𝓞 K) : K))| ≤ Y := by sorry
