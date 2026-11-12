-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorOneQubitPreparation_mapDensity
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitPreparation_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:26:19.058188+00:00
-- url     : https://prove2.me/theorems/e6b793cd-a9a0-472b-8501-3b42393cffd0
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor One Qubit Preparation map Density
-- statement:
--   Pointwise action of the physical one-qubit successor preparation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L377-L383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L377-L383

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
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
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitPreparation_mapDensity
    (rho : DensityOperator QubitSpace) :
    decodedRetryPoolSuccessorOneQubitPreparation.mapDensity rho =
      (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm.conjDensity
        (aBasisDephasing.mapDensity rho) := by sorry
