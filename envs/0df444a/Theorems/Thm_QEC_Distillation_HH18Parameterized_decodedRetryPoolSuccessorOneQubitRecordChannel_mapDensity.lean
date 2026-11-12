-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorOneQubitRecordChannel_mapDensity
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitRecordChannel_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:53:23.55747+00:00
-- url     : https://prove2.me/theorems/40cbb237-349e-4723-930c-e1fa70886ea8
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor One Qubit Record Channel map Density
-- statement:
--   The inverse-phase resource handoff followed by the forward resource
--   rotation cancels exactly, leaving the genuine A-dephasing and outcome-record
--   transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean#L53-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean#L53-L64

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Definitions.Def_QEC_Semantics_Instruments_Registers_ChannelProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitRecordChannel_mapDensity
    (rho : DensityOperator QubitSpace) :
    decodedRetryPoolSuccessorOneQubitRecordChannel.mapDensity rho =
      aBasisTransport.symm.conjDensity (aBasisDephasing.mapDensity rho) := by sorry
