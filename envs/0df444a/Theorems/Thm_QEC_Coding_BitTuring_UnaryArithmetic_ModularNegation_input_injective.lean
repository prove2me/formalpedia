-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:11:09.854592+00:00
-- url     : https://prove2.me/theorems/05e74a02-7e35-4113-9e3f-a9f2795441cc
-- title:
--   Modular Negation: input injective
-- statement:
--   The encoded input distinguishes every non-proof domain parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularNegation.lean#L250-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularNegation.lean#L250-L255

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Mathlib.Data.ZMod.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularNegation
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation.input_injective : Function.Injective input := by sorry
