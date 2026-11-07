-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_card_sub_card_le_finrank_middleHomology
-- name    : QEC.Coding.ExpanderCodes.PK20.card_sub_card_le_finrank_middleHomology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:39:55.877339+00:00
-- url     : https://prove2.me/theorems/cb34c3ed-ae1c-4b5b-a231-d60057080dbf
-- title:
--   PK20: card sub card le finrank middle Homology
-- statement:
--   The quotient Tanner kernel injects at the level of dimensions into the
--   full odd cyclic lifted product.  Rank-nullity therefore supplies the lower
--   half of the source dimension estimate without a rank assumption on `A(1)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L409-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L409-L443

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.card_sub_card_le_finrank_middleHomology
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aCol - Fintype.card aRow ≤
      Module.finrank (ZMod 2)
        (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology := by sorry
