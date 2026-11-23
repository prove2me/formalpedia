-- Prove2me | Theorems.Thm_SumProduct_latticeEmbed_apply
-- name    : SumProduct.latticeEmbed_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:49:05.799798+00:00
-- url     : https://prove2.me/theorems/4917ae76-c02a-4d7a-8c59-7f8853970274
-- title:
--   Sum Product: lattice Embed apply
-- statement:
--   The Sum Product construction uses the lattice Embed apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L225-L226
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L225-L226

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct

theorem SumProduct.latticeEmbed_apply {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) :
    latticeEmbed K α = NumberField.mixedEmbedding K (algebraMap (𝓞 K) K α) := by sorry

attribute [defeq] SumProduct.latticeEmbed_apply
