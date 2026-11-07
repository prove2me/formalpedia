-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_RippleCounter_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:17:06.865364+00:00
-- url     : https://prove2.me/theorems/03eec44b-5ec6-4c5c-a7cb-4e38686b07ee
-- title:
--   Ripple Counter: input injective
-- statement:
--   Finite counter instructions/configurations and counted clean body execution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryRippleCounter.lean#L573-L578
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryRippleCounter.lean#L573-L578

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.input_injective (n:ℕ):Function.Injective (input n):= by sorry
