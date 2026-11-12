-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:58:36.643642+00:00
-- url     : https://prove2.me/theorems/922a184e-ae93-4846-993a-528e23fb663c
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Prepare Resources noisy Resources
-- statement:
--   The actual flat noisy resource family prepares precisely the genuine root
--   input used by the complete retry-protocol Born-mass theorems.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Run.lean#L94-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Run.lean#L94-L106

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources
    (m w z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalProtocolPrepareResources m w
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) rhoUnit
        (decodedRetryPoolPhysicalProtocolNoisyResources m w z q hz epsilon) =
      decodedRetryPoolPhysicalProtocolNoisyRootInput m w z q hz epsilon
        rhoUnit := by sorry
