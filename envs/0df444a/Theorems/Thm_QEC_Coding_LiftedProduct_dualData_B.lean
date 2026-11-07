-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_dualData_B
-- name    : QEC.Coding.LiftedProduct.dualData_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:47.62021+00:00
-- url     : https://prove2.me/theorems/e83d44d1-2595-4eba-978f-f0a907a61470
-- title:
--   Lifted Product: dual Data B
-- statement:
--   The Lifted Product construction uses the dual Data B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L110-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L110-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.dualData_B
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : Data F G aRow aCol bRow bCol) :
    (dualData D).B = starTranspose D.B := by sorry

attribute [defeq] QEC.Coding.LiftedProduct.dualData_B
