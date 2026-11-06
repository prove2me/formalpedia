-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_leftRegularMatrix_starTranspose_entry
-- name    : QEC.Coding.LiftedProduct.leftRegularMatrix_starTranspose_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:29:39.837639+00:00
-- url     : https://prove2.me/theorems/44d3d2f3-3018-4138-b393-fb97fcd1200c
-- title:
--   Lifted Product: left Regular Matrix star Transpose entry
-- statement:
--   Entrywise bridge from the matrix dual to transposed left regular blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L286-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L286-L291

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.leftRegularMatrix_starTranspose_entry {F G m n : Type*}
    [Semiring F] [Group G] (M : Matrix m n (MonoidAlgebra F G))
    (i : m) (j : n) :
    leftRegularMatrix ((starTranspose M) j i) =
      (leftRegularMatrix (M i j)).transpose := by sorry
