-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inr_apply
-- name    : QEC.Coding.LiftedProduct.signedSwapWord_inr_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:44.349527+00:00
-- url     : https://prove2.me/theorems/143fc919-5ef4-40b8-a8ef-1ad46b40ac6c
-- title:
--   Lifted Product: signed Swap Word inr apply
-- statement:
--   The Lifted Product construction uses the signed Swap Word inr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L30-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L30-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.signedSwapWord_inr_apply {F A B : Type*} [Neg F]
    (z : Word F (Sum A B)) (a : A) :
    signedSwapWord z (Sum.inr a) = -z (Sum.inl a) := by sorry

attribute [defeq] QEC.Coding.LiftedProduct.signedSwapWord_inr_apply
