-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularProduct.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:09:33.354287+00:00
-- url     : https://prove2.me/theorems/913d8d94-242f-4414-bc1d-896dfe8c4d65
-- title:
--   Modular Product: input injective
-- statement:
--   The positive-modulus triple encoding distinguishes every valid input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularProduct.lean#L410-L416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularProduct.lean#L410-L416

import Definitions.Def_QEC_Coding_BitTuring_UnaryRemainder
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularProduct
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularProduct.input_injective : Function.Injective input := by sorry
