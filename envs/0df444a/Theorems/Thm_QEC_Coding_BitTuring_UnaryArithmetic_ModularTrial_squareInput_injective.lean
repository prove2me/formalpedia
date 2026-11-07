-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularTrial_squareInput_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.squareInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:09:19.736479+00:00
-- url     : https://prove2.me/theorems/dd6fc192-fc11-47e7-adc6-51de9b3ecd65
-- title:
--   Modular Trial: square Input injective
-- statement:
--   Duplicated-operand positive-modulus body inputs are faithful.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean#L82-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean#L82-L86

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.squareInput_injective : Function.Injective squareInput := by sorry
