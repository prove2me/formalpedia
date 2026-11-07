-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PSLComparison_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:39:40.299619+00:00
-- url     : https://prove2.me/theorems/f69462bf-7065-44d0-930a-9debc5bf9e63
-- title:
--   PSLComparison: input injective
-- statement:
--   Actual finite instructions or proved execution invariant, whole budget or original source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPSLComparison.lean#L304-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPSLComparison.lean#L304-L314

import Definitions.Def_QEC_Coding_BitTuring_UnaryPSLComparisonSupport
import Definitions.Def_QEC_Coding_BitTuring_UnaryPSLComparison
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularAdjugate_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
open QEC.Coding.BitTuring.UnaryArithmetic.PSLComparisonSupport

theorem QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.input_injective : Function.Injective input := by sorry
