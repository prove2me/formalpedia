-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SignedCoefficient_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:16:11.697195+00:00
-- url     : https://prove2.me/theorems/06b86497-b7bb-47fb-9840-274e7c77cec2
-- title:
--   Signed Coefficient: input injective
-- statement:
--   Actual finite program, proved transition invariant or certificate in the complete closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySignedCoefficient.lean#L79-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySignedCoefficient.lean#L79-L84

import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularNegation
import Definitions.Def_QEC_Coding_BitTuring_UnarySignedCoefficient
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient.input_injective (c:ℤ) : Function.Injective (@input c) := by sorry
