-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_boundary1_rank_lowerBound
-- name    : QEC.Coding.BalancedProduct.CyclicDimension.boundary1_rank_lowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:32.474412+00:00
-- url     : https://prove2.me/theorems/fb1fc627-83e9-4433-baa4-ca7f2f632264
-- title:
--   Cyclic Dimension: boundary1 rank lower Bound
-- statement:
--   Rank lower bound for the first boundary, obtained from its vertical
--   cyclic block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L188-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L188-L203

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u

theorem QEC.Coding.BalancedProduct.CyclicDimension.boundary1_rank_lowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aRow * (q - 1) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (LiftedProduct.boundary1 (Cyclic.data q A))) := by sorry
