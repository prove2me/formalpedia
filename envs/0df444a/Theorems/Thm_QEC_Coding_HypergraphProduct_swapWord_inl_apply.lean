-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_inl_apply
-- name    : QEC.Coding.HypergraphProduct.swapWord_inl_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:32:39.760075+00:00
-- url     : https://prove2.me/theorems/1805b11a-5303-478c-a16f-a196cd126207
-- title:
--   Hypergraph Product: swap Word inl apply
-- statement:
--   The Hypergraph Product construction uses the swap Word inl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L25-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L25-L26

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.swapWord_inl_apply {F A B : Type*} (x : Word F (Sum A B)) (b : B) :
    swapWord x (Sum.inl b) = x (Sum.inr b) := by sorry

attribute [defeq] QEC.Coding.HypergraphProduct.swapWord_inl_apply
