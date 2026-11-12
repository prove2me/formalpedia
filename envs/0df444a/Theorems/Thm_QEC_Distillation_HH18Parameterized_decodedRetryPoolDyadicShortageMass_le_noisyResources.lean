-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolDyadicShortageMass_le_noisyResources
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicShortageMass_le_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:08:21.685989+00:00
-- url     : https://prove2.me/theorems/b64945df-ff92-4110-8dec-7bc017004507
-- title:
--   HH18 Parameterized: decoded Retry Pool Dyadic Shortage Mass le noisy Resources
-- statement:
--   The actual decoded retry-pool shortage on the source-derived dyadic number
--   of attempts is bounded by the derived dyadic physical slack.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L170-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L170-L221

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicShortageMass_le_noisyResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (stage required : Nat) :
    decodedRetryPoolShortageMass h hdegree
        (decodedRetryPoolDyadicAttempts stage required) required
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          (decodedRetryPoolDyadicAttempts stage required)) ≤
      (decodedRetryPoolDyadicDenominator stage : ℝ) *
        physicalInputCount m w * epsilon.1 := by sorry
