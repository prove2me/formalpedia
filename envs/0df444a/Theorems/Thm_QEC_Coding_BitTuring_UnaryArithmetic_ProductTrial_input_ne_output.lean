-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ProductTrial_input_ne_output
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial.input_ne_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:10:32.530252+00:00
-- url     : https://prove2.me/theorems/ee3400ac-46cf-40fc-ab45-ffde5f4083f0
-- title:
--   Product Trial: input ne output
-- statement:
--   The actual composed body has disjoint input and output channels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryProductTrial.lean#L394-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryProductTrial.lean#L394-L395

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_UnaryProductTrial
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRootTrial_input_ne_output

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial.input_ne_output : machine.input≠machine.output := by sorry
