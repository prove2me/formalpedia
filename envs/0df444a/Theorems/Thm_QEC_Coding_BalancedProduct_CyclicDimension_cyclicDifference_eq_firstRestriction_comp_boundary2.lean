-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_cyclicDifference_eq_firstRestriction_comp_boundary2
-- name    : QEC.Coding.BalancedProduct.CyclicDimension.cyclicDifference_eq_firstRestriction_comp_boundary2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:47.588209+00:00
-- url     : https://prove2.me/theorems/349cc051-4ad1-4e19-b5fa-143832a8b1c2
-- title:
--   Cyclic Dimension: cyclic Difference eq first Restriction comp boundary2
-- statement:
--   The second lifted boundary contains the cyclic difference on its
--   horizontal output block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L155-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L155-L184

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u

theorem QEC.Coding.BalancedProduct.CyclicDimension.cyclicDifference_eq_firstRestriction_comp_boundary2
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    cyclicDifference q aCol =
      (LiftedProduct.firstRestriction (Cyclic.data q A)).comp
        (LiftedProduct.boundary2 (Cyclic.data q A)) := by sorry
