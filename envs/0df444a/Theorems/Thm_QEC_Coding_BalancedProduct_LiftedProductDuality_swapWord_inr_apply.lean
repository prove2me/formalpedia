-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inr_apply
-- name    : QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:06:33.072829+00:00
-- url     : https://prove2.me/theorems/ce4eedab-6d4d-47e2-89c2-90c283ccedf5
-- title:
--   Lifted Product Duality: swap Word inr apply
-- statement:
--   The Lifted Product Duality construction uses the swap Word inr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L31-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L31-L33

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v

theorem QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply {F A B : Type*}
    (z : Word F (Sum A B)) (a : A) :
    swapWord z (Sum.inr a) = z (Sum.inl a) := by sorry

attribute [defeq] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply
