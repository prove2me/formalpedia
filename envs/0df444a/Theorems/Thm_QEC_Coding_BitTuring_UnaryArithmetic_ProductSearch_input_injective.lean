-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ProductSearch_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:40:32.157504+00:00
-- url     : https://prove2.me/theorems/c7386ca5-cf8a-43a2-9b70-1e6cfdc3701c
-- title:
--   Product Search: input injective
-- statement:
--   The complete tape encoding distinguishes the target, fixed factor and modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryProductSearch.lean#L150-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryProductSearch.lean#L150-L157

import Definitions.Def_QEC_Coding_BitTuring_UnaryProductTrial
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Definitions.Def_QEC_Coding_BitTuring_UnaryProductSearch
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRoot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch
open Turing StateTransition
open SquareRoot (readNat afterNat readNat_prefix afterNat_prefix readNat_unary state_succ_after)

theorem QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch.input_injective : Function.Injective input := by sorry
