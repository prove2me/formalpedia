-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:34:44.60903+00:00
-- url     : https://prove2.me/theorems/cd39ce9b-2d7b-418a-b41f-0d746a3d8113
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Regroup Transport apply basis
-- statement:
--   The regrouping transport maps every flat computational basis vector to
--   the corresponding literal nested tensor basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L206-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L206-L221

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupTransport_apply_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) :
    decodedRetryPoolSuccessorRegroupTransport m w z q stage hstage
      (EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
        Complex bits) =
      tensorPowerBasis
        (tensorPowerBasis
          (EuclideanSpace.basisFun (Qubit.Bitstring (PhysicalSite m w)) Complex)
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
        (logicalOutputCount m w)
        (decodedRetryPoolSuccessorRegroupBitstringEquiv m w z q stage hstage bits) := by sorry
