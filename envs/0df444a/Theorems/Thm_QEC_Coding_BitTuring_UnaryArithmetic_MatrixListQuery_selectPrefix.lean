-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_MatrixListQuery_selectPrefix
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery.selectPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:15:08.094283+00:00
-- url     : https://prove2.me/theorems/8d44fb88-a963-4032-aed0-6f9b3e19d95a
-- title:
--   Matrix List Query: select Prefix
-- statement:
--   Actual finite instruction construction or proved invariant, whole execution, budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMatrixListQuery.lean#L72-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMatrixListQuery.lean#L72-L85

import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery.selectPrefix (n i:ℕ) (xs:List ℕ) (q:ℕ) (hi:i+xs.length=n) :
    fields n (prefixMask n) i (xs++[q])=xs := by sorry
