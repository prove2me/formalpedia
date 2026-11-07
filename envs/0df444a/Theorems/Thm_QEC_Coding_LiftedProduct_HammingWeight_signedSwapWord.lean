-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_HammingWeight_signedSwapWord
-- name    : QEC.Coding.LiftedProduct.HammingWeight_signedSwapWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:13:11.2187+00:00
-- url     : https://prove2.me/theorems/e35a4038-afbf-4a36-bbe8-cddd80123e57
-- title:
--   Lifted Product: Hamming Weight signed Swap Word
-- statement:
--   Signed block exchange preserves Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L66-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L66-L90

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.HammingWeight_signedSwapWord
    {F A B : Type*} [AddGroup F] [DecidableEq F]
    [Fintype A] [Fintype B] (z : Word F (Sum A B)) :
    HammingWeight (signedSwapWord z) = HammingWeight z := by sorry
