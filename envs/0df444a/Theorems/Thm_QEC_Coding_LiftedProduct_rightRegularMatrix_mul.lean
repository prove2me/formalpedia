-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_rightRegularMatrix_mul
-- name    : QEC.Coding.LiftedProduct.rightRegularMatrix_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:31:06.764255+00:00
-- url     : https://prove2.me/theorems/d05fcd47-bf24-4b83-b83b-5d2076029dd9
-- title:
--   Lifted Product: right Regular Matrix mul
-- statement:
--   The right regular matrix reverses convolution order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L184-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L184-L196

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.rightRegularMatrix_mul {F G : Type*}
    [CommSemiring F] [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra F G) :
    rightRegularMatrix (a * b) = rightRegularMatrix b * rightRegularMatrix a := by sorry
