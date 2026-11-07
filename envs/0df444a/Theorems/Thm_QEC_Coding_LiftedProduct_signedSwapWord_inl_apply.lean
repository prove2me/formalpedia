-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inl_apply
-- name    : QEC.Coding.LiftedProduct.signedSwapWord_inl_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:27.242195+00:00
-- url     : https://prove2.me/theorems/251fd82c-4a8d-4803-9a1c-6adbe4e31457
-- title:
--   Lifted Product: signed Swap Word inl apply
-- statement:
--   The Lifted Product construction uses the signed Swap Word inl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L25-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L25-L27

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.signedSwapWord_inl_apply {F A B : Type*} [Neg F]
    (z : Word F (Sum A B)) (b : B) :
    signedSwapWord z (Sum.inl b) = z (Sum.inr b) := by sorry

attribute [defeq] QEC.Coding.LiftedProduct.signedSwapWord_inl_apply
