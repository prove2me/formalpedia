-- Prove2me | Theorems.Thm_SumProduct_normAtPlace_latticeEmbed
-- name    : SumProduct.normAtPlace_latticeEmbed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:57:05.035033+00:00
-- url     : https://prove2.me/theorems/14de41c2-a943-4604-bc69-f2e1ded9973f
-- title:
--   Sum Product: norm At Place lattice Embed
-- statement:
--   The Sum Product construction uses the norm At Place lattice Embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L233-L235
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L233-L235

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem SumProduct.normAtPlace_latticeEmbed {K : Type*} [Field K] [NumberField K] (α : 𝓞 K)
    (w : InfinitePlace K) : normAtPlace w (latticeEmbed K α) = w (α : K) := by sorry
