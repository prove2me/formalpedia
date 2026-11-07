-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_QuaternionAssembly_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:18:11.451974+00:00
-- url     : https://prove2.me/theorems/6d0cab89-bd63-4a78-bb3a-183311cddf36
-- title:
--   Quaternion Assembly: input injective
-- statement:
--   Actual finite program or proved selector, execution, budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryQuaternionMatrix.lean#L436-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryQuaternionMatrix.lean#L436-L447

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
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularAdjugate_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularSum_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
open Turing StateTransition FieldProjection
open Turing StateTransition FieldProjection
open Turing FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly.input_injective : Function.Injective input := by sorry
