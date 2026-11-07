-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularTrial_squareTrialInput_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.squareTrialInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:14:58.435196+00:00
-- url     : https://prove2.me/theorems/adc8d4b8-2a8e-42c4-aaf5-142ee1a2d0fe
-- title:
--   Modular Trial: square Trial Input injective
-- statement:
--   The full square trial input distinguishes operand, positive modulus and target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean#L120-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean#L120-L122

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.squareTrialInput_injective :
    Function.Injective (UnaryOutputEquality.input squareInput) := by sorry
