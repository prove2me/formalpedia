-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_neg
-- name    : QEC.Coding.LiftedProduct.signedSwapWord_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:36.585116+00:00
-- url     : https://prove2.me/theorems/9abb7193-8fdb-40a0-a640-98e1107b9201
-- title:
--   Lifted Product: signed Swap Word neg
-- statement:
--   The Lifted Product construction uses the signed Swap Word neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L42-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L42-L46

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.signedSwapWord_neg {F A B : Type*} [AddGroup F]
    (z : Word F (Sum A B)) :
    signedSwapWord (-z) = -signedSwapWord z := by sorry
