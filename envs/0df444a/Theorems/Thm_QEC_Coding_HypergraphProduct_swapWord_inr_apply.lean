-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_inr_apply
-- name    : QEC.Coding.HypergraphProduct.swapWord_inr_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:32:59.919629+00:00
-- url     : https://prove2.me/theorems/0fda4482-b491-429e-8fc1-9a0c9546aab5
-- title:
--   Hypergraph Product: swap Word inr apply
-- statement:
--   The Hypergraph Product construction uses the swap Word inr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L29-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L29-L30

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.swapWord_inr_apply {F A B : Type*} (x : Word F (Sum A B)) (a : A) :
    swapWord x (Sum.inr a) = x (Sum.inl a) := by sorry

attribute [defeq] QEC.Coding.HypergraphProduct.swapWord_inr_apply
