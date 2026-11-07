-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularAdjugate_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:16:26.555096+00:00
-- url     : https://prove2.me/theorems/8a2be399-b42e-4f5d-ae17-44f3d4b4a4c9
-- title:
--   Modular Adjugate: input injective
-- statement:
--   The encoded input distinguishes every non-proof domain parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularAdjugate.lean#L230-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularAdjugate.lean#L230-L241

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularNegation
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
open Turing
open FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate.input_injective : Function.Injective input := by sorry
