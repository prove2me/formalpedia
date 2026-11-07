-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_QuaternionAssembly_output_eq_field
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly.output_eq_field
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:15:59.607059+00:00
-- url     : https://prove2.me/theorems/99cd44be-2aa9-4ec9-b459-3b5c94507f61
-- title:
--   Quaternion Assembly: output eq field
-- statement:
--   Exact canonical field values computed by the whole actual arithmetic assembly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryQuaternionMatrix.lean#L412-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryQuaternionMatrix.lean#L412-L418

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
open Turing StateTransition FieldProjection
open Turing StateTransition FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly.output_eq_field (q:ℕ) (hq:0<q) (s y d c b a:ZMod q) :
    output s.val y.val d.val c.val b.val a.val q=raw
      [((y*d+a)*s).val,((-(y*b)+c)*s).val,((-c+-(y*b))*s).val,((-(y*d)+a)*s).val] := by sorry
