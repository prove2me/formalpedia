-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolShortageMass_markov_le_noisyResources
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolShortageMass_markov_le_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:04:12.477526+00:00
-- url     : https://prove2.me/theorems/73dcdfd1-dbc0-4ad0-8098-5c7012bf88a3
-- title:
--   HH18 Parameterized: decoded Retry Pool Shortage Mass markov le noisy Resources
-- statement:
--   The actual finite decoded HH18 retry-pool shortage mass on recursively
--   tensorized noisy physical inputs is bounded by its rejected one-block mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/FirstMoment.lean#L75-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/FirstMoment.lean#L75-L97

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolFirstMomentClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolShortageMass_markov_le_noisyResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (attempts required : Nat) (hrequired : required ≤ attempts) :
    ((attempts - required + 1 : Nat) : ℝ) *
        decodedRetryPoolShortageMass h hdegree attempts required
          (tensorPowerProductInput
            (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit attempts) ≤
      (attempts : ℝ) * (1 - acceptedBernoulliMass w r m epsilon) := by sorry
