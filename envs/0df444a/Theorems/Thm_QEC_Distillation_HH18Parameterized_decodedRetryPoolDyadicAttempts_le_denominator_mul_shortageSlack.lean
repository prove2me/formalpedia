-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolDyadicAttempts_le_denominator_mul_shortageSlack
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicAttempts_le_denominator_mul_shortageSlack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:07:07.456503+00:00
-- url     : https://prove2.me/theorems/a4827ab4-6f07-4bbc-8892-3df0a4660ae3
-- title:
--   HH18 Parameterized: decoded Retry Pool Dyadic Attempts le denominator mul shortage Slack
-- statement:
--   The derived attempt count is controlled by the denominator times the
--   finite shortage slack that appears in the Markov bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L91-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L91-L134

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolDyadicSlackClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicAttempts_le_denominator_mul_shortageSlack
    (stage required : Nat) :
    decodedRetryPoolDyadicAttempts stage required ≤
      decodedRetryPoolDyadicDenominator stage *
        (decodedRetryPoolDyadicAttempts stage required - required + 1) := by sorry
