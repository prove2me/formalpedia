-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorReindexChannel_rankOne_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorReindexChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:16:00.801017+00:00
-- url     : https://prove2.me/theorems/d948f48e-fbce-4f75-a1a9-e8331bbabb55
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Reindex Channel rank One basis
-- statement:
--   The complete successor reindexing sends every source computational matrix
--   unit to the corresponding target computational matrix unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L233-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L233-L291

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorReindexChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (left right : Qubit.Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorReindexChannel m w z q stage hstage
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorSourceSlots m w z q stage))
            Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorSourceSlots m w z q stage))
            Complex right)).toLinearMap =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun
          (Qubit.Bitstring
            (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
          Complex
          (decodedRetryPoolSuccessorBitstringEquiv
            m w z q stage hstage left))
        (EuclideanSpace.basisFun
          (Qubit.Bitstring
            (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
          Complex
          (decodedRetryPoolSuccessorBitstringEquiv
            m w z q stage hstage right))).toLinearMap := by sorry
