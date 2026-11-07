-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_DeterminantPredicate_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:40:36.273792+00:00
-- url     : https://prove2.me/theorems/56e77f8b-0b2d-420a-adbf-fe0235fea7d7
-- title:
--   Determinant Predicate: input injective
-- statement:
--   Actual finite instructions or proved determinant invariant, whole budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryDeterminantPredicate.lean#L190-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryDeterminantPredicate.lean#L190-L200

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryDeterminantPredicate
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularAdjugate_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularSum_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_QuaternionAssembly_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection QuaternionAssembly

theorem QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate.input_injective:Function.Injective input:= by sorry
