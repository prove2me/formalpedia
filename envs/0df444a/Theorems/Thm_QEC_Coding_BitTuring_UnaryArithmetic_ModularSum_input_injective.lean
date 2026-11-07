-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularSum_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularSum.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:09:42.144212+00:00
-- url     : https://prove2.me/theorems/81c92565-43de-4c22-9f72-c2ba39d71e7e
-- title:
--   Modular Sum: input injective
-- statement:
--   The positive-modulus triple encoding distinguishes every valid input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularSum.lean#L205-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularSum.lean#L205-L211

import Definitions.Def_QEC_Coding_BitTuring_UnaryRemainder
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularSum
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularSum.input_injective : Function.Injective input := by sorry
