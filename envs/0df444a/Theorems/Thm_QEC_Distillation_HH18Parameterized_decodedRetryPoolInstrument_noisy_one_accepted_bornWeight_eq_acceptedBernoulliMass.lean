-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_noisy_one_accepted_bornWeight_eq_acceptedBernoulliMass
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_noisy_one_accepted_bornWeight_eq_acceptedBernoulliMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:33:07.930257+00:00
-- url     : https://prove2.me/theorems/8ea89b12-8108-489e-a4f6-0bc3766ddebb
-- title:
--   HH18 Parameterized: decoded Retry Pool Instrument noisy one accepted born Weight eq accepted Bernoulli Mass
-- statement:
--   The accepted observed history of one noisy physical block has exactly the
--   existing parameterized accepted Bernoulli mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L225-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L225-L240

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_noisy_one_accepted_bornWeight_eq_acceptedBernoulliMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolInstrument h hdegree 1 1).bornWeight
        ⟨(.accepted, PUnit.unit), PUnit.unit⟩
          (tensorPowerProductInput
            (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit 1) =
      acceptedBernoulliMass w r m epsilon := by sorry
