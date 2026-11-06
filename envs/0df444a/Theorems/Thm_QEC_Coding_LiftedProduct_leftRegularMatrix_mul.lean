-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_leftRegularMatrix_mul
-- name    : QEC.Coding.LiftedProduct.leftRegularMatrix_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:29:45.683046+00:00
-- url     : https://prove2.me/theorems/16d9ae9f-a7b5-4343-b5eb-1707ddf5c957
-- title:
--   Lifted Product: left Regular Matrix mul
-- statement:
--   The left regular matrix preserves convolution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L169-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L169-L181

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.leftRegularMatrix_mul {F G : Type*}
    [CommSemiring F] [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra F G) :
    leftRegularMatrix (a * b) = leftRegularMatrix a * leftRegularMatrix b := by sorry
