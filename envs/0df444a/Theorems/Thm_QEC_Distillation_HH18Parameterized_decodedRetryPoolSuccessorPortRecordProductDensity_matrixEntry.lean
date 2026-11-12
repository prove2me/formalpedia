-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorPortRecordProductDensity_matrixEntry
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortRecordProductDensity_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:02:36.03035+00:00
-- url     : https://prove2.me/theorems/7cbd6896-6a32-4ddf-94e0-e3fe5f66ad3f
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Port Record Product Density matrix Entry
-- statement:
--   Computational entries of the routed fixed-port product factor over its
--   actual next-stage trial/physical coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L242-L396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L242-L396

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortRecordProductDensity_matrixEntry
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (parameter : ErrorParameter)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (left right : Bitstring
      (Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
        PhysicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun
          (Bitstring
            (Fin (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) Complex left)
        ((decodedRetryPoolSuccessorPortRecordProductDensity
          m w z q stage hstage parameter rhoUnit).toOperator
          (EuclideanSpace.basisFun
            (Bitstring
              (Fin (decodedRetryPoolBackwardAttempts m w z q
                  ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) Complex right)) =
      ∏ coordinate :
          Fin (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w,
        inner Complex
          (EuclideanSpace.basisFun (Fin 2) Complex (left coordinate))
          ((decodedRetryPoolOneQubitRecordDensity parameter).toOperator
            (EuclideanSpace.basisFun (Fin 2) Complex (right coordinate))) := by sorry
