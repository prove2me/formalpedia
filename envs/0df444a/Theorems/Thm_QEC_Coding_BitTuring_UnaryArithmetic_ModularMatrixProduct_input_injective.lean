-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularMatrixProduct_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:40:25.244443+00:00
-- url     : https://prove2.me/theorems/60207d32-aa0e-46b5-ad46-ffdddeaa040a
-- title:
--   Modular Matrix Product: input injective
-- statement:
--   The actual encoding distinguishes every domain input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMatrixProduct.lean#L244-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMatrixProduct.lean#L244-L255

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularDot
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixProduct
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularDot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularSum_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct
open Turing
open FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct.input_injective : Function.Injective input := by sorry
