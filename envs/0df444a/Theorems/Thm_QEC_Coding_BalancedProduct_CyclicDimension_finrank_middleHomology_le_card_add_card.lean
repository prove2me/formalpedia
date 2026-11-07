-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_finrank_middleHomology_le_card_add_card
-- name    : QEC.Coding.BalancedProduct.CyclicDimension.finrank_middleHomology_le_card_add_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:01:29.069709+00:00
-- url     : https://prove2.me/theorems/2c3b6976-8226-4fef-ac5d-1981c964e62d
-- title:
--   Cyclic Dimension: finrank middle Homology le card add card
-- statement:
--   Tanner-matrix-independent upper bound on the number of encoded qubits in
--   the cyclic lifted product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L228-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L228-L274

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u

theorem QEC.Coding.BalancedProduct.CyclicDimension.finrank_middleHomology_le_card_add_card
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Module.finrank (ZMod 2)
        (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ≤
      Fintype.card aCol + Fintype.card aRow := by sorry
