-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_DeterminantPredicate_result_eq_det
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate.result_eq_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:16:33.408513+00:00
-- url     : https://prove2.me/theorems/3bce0d42-39d8-4c3c-b6d9-5b8efdae3c4a
-- title:
--   Determinant Predicate: result eq det
-- statement:
--   Actual finite instructions or proved determinant invariant, whole budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryDeterminantPredicate.lean#L168-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryDeterminantPredicate.lean#L168-L176

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryDeterminantPredicate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection QuaternionAssembly

theorem QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate.result_eq_det (q:ℕ) (hq:0<q) (a b c d:ZMod q) :
    result a.val b.val c.val d.val q=(!![a,b;c,d]).det.val := by sorry
