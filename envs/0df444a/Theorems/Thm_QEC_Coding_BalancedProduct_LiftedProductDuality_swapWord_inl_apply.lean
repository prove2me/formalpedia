-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inl_apply
-- name    : QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:06:49.73301+00:00
-- url     : https://prove2.me/theorems/f7bf9958-fd0e-483b-8e61-49bce89f6413
-- title:
--   Lifted Product Duality: swap Word inl apply
-- statement:
--   The Lifted Product Duality construction uses the swap Word inl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L26-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L26-L28

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v

theorem QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply {F A B : Type*}
    (z : Word F (Sum A B)) (b : B) :
    swapWord z (Sum.inl b) = z (Sum.inr b) := by sorry

attribute [defeq] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply
