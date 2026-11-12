-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolDyadicEnoughMass_noisyResources_lower_bound
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicEnoughMass_noisyResources_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:08:31.214638+00:00
-- url     : https://prove2.me/theorems/764078b8-e980-4b78-b869-c6dfd375b8f4
-- title:
--   HH18 Parameterized: decoded Retry Pool Dyadic Enough Mass noisy Resources lower bound
-- statement:
--   The complementary actual enough mass inherits the source-derived dyadic
--   lower bound from the finite shortage estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L225-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L225-L244

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicEnoughMass_noisyResources_lower_bound
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (stage required : Nat) :
    1 - (decodedRetryPoolDyadicDenominator stage : ℝ) *
        physicalInputCount m w * epsilon.1 ≤
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolDyadicAttempts stage required) required
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          (decodedRetryPoolDyadicAttempts stage required)) := by sorry
