-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:23:36.667016+00:00
-- url     : https://prove2.me/theorems/3dacdc93-861a-404a-ad91-b6f7f61c7d68
-- title:
--   HH18 Parameterized: decoded Retry Pool Qubit Tensor Power Register Transport symm apply basis
-- statement:
--   Undoing the canonical finite-register transport sends a computational
--   basis vector to the recursive tensor basis with its exact inverse label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L105-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L105-L117

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis
    (ι : Type) [Fintype ι] [DecidableEq ι] (bits : Bitstring ι) :
    (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm
        (EuclideanSpace.basisFun (Bitstring ι) Complex bits) =
      tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
        (Fintype.card ι)
        ((decodedRetryPoolQubitTensorPowerBitstringEquiv ι).symm bits) := by sorry
