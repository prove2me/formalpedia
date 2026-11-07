-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_cyclicDifference_eq_boundary1_comp_secondZeroExtension
-- name    : QEC.Coding.BalancedProduct.CyclicDimension.cyclicDifference_eq_boundary1_comp_secondZeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:39.040112+00:00
-- url     : https://prove2.me/theorems/1097a6b9-e50a-4142-b0fd-dea060fc053f
-- title:
--   Cyclic Dimension: cyclic Difference eq boundary1 comp second Zero Extension
-- statement:
--   The first lifted boundary contains the cyclic difference on its vertical
--   qubit block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L129-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L129-L151

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u

theorem QEC.Coding.BalancedProduct.CyclicDimension.cyclicDifference_eq_boundary1_comp_secondZeroExtension
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    cyclicDifference q aRow =
      (LiftedProduct.boundary1 (Cyclic.data q A)).comp
        (LiftedProduct.secondZeroExtension (Cyclic.data q A)) := by sorry
