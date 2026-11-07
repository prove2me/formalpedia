-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRootTrial_input_ne_output
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial.input_ne_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:08:52.098003+00:00
-- url     : https://prove2.me/theorems/57f2af17-e8f1-47d2-9f0f-7602dcb96a95
-- title:
--   Square Root Trial: input ne output
-- statement:
--   The actual composed body has disjoint input and output channels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySquareRootTrial.lean#L413-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySquareRootTrial.lean#L413-L414

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial.input_ne_output : machine.input≠machine.output := by sorry
