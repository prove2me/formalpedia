-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_dropWhile
-- name    : QEC.Coding.BitTuring.UnaryOutputEquality.prefixInput_dropWhile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:06:10.086021+00:00
-- url     : https://prove2.me/theorems/e62089c8-518f-4910-b7f8-4fc2c8aa0eb5
-- title:
--   Unary Output Equality: prefix Input drop While
-- statement:
--   Recover the unchanged payload after the actual target delimiter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryOutputEquality.lean#L287-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryOutputEquality.lean#L287-L291

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryOutputEquality
open Turing StateTransition UnaryArithmetic
variable (A : Machine)

theorem QEC.Coding.BitTuring.UnaryOutputEquality.prefixInput_dropWhile (r : ℕ) (x : List Bool) :
    (prefixInput r x).dropWhile id=false::x := by sorry
