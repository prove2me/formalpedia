-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularTrial_productInput_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.productInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:09:13.594741+00:00
-- url     : https://prove2.me/theorems/47e33fab-be21-49d5-bac9-6f0ee04e4368
-- title:
--   Modular Trial: product Input injective
-- statement:
--   The full product trial input distinguishes operands, positive modulus and target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean#L115-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean#L115-L117

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.productInput_injective :
    Function.Injective (UnaryOutputEquality.input ModularProduct.input) := by sorry
