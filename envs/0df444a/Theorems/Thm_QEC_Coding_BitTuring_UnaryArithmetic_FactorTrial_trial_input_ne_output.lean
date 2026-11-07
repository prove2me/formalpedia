-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTrial_trial_input_ne_output
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial.trial_input_ne_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:09:52.95326+00:00
-- url     : https://prove2.me/theorems/6c832b52-0780-4431-bc2e-6a60a8b0d893
-- title:
--   Factor Trial: trial input ne output
-- statement:
--   The Factor Trial construction uses the trial input ne output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTrial.lean#L559-L560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTrial.lean#L559-L560

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial.trial_input_ne_output : trialMachine.input ≠ trialMachine.output := by sorry
