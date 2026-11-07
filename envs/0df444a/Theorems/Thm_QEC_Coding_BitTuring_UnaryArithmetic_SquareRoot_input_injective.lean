-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRoot_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:16:30.310277+00:00
-- url     : https://prove2.me/theorems/def1329d-2345-411d-9cc5-224326c6c071
-- title:
--   Square Root: input injective
-- statement:
--   The actual input encoding distinguishes every target and modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySquareRoot.lean#L180-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySquareRoot.lean#L180-L186

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot.input_injective : Function.Injective input := by sorry
