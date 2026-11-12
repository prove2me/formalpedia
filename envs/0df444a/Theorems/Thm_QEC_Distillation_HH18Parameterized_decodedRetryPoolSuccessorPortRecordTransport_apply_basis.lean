-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorPortRecordTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortRecordTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:39:42.556197+00:00
-- url     : https://prove2.me/theorems/8fc5a341-3e13-41b5-9693-87db91250681
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Port Record Transport apply basis
-- statement:
--   The fixed-port successor transport maps every computational basis vector
--   to the basis vector at its exact next-stage coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L85-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L85-L99

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
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
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortRecordTransport_apply_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Bitstring (Fin (decodedRetryPoolBackwardSchedule m w z q stage))) :
    decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
        (EuclideanSpace.basisFun
          (Bitstring (Fin (decodedRetryPoolBackwardSchedule m w z q stage)))
          Complex bits) =
      EuclideanSpace.basisFun
        (Bitstring
          (Fin (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) Complex
        (decodedRetryPoolSuccessorPortRecordBitstringEquiv
          m w z q stage hstage bits) := by sorry
