-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_boundary2_rank_lowerBound
-- name    : QEC.Coding.BalancedProduct.CyclicDimension.boundary2_rank_lowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:18.762497+00:00
-- url     : https://prove2.me/theorems/f87e86f1-1675-4bc2-9497-13a807537c41
-- title:
--   Cyclic Dimension: boundary2 rank lower Bound
-- statement:
--   Rank lower bound for the second boundary.  Postcomposition cannot raise
--   rank, so the visible horizontal cyclic block is a lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L207-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L207-L224

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u

theorem QEC.Coding.BalancedProduct.CyclicDimension.boundary2_rank_lowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aCol * (q - 1) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (LiftedProduct.boundary2 (Cyclic.data q A))) := by sorry
