-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupBranchChannel_rankOne_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupBranchChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:54:04.32491+00:00
-- url     : https://prove2.me/theorems/110e7562-4933-41c6-a96b-270d8c8309ce
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Regroup Branch Channel rank One basis
-- statement:
--   On a flat computational matrix unit, the physical outer-branch selector
--   retains the exact trial/physical record at that logical port and contracts
--   every discarded logical branch by its full computational-basis inner product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L341-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L341-L393

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupBranchChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (branch : Fin (logicalOutputCount m w))
    (left right : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) :
    decodedRetryPoolSuccessorRegroupBranchChannel
        m w z q stage hstage branch
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
            Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
            Complex right)).toLinearMap =
      (∏ coordinate : Fin (logicalOutputCount m w),
          if coordinate = branch then 1
          else inner Complex
            (tensorPowerBasis
              (EuclideanSpace.basisFun
                (Qubit.Bitstring (PhysicalSite m w)) Complex)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)
              (decodedRetryPoolSuccessorPortTrialHistory
                m w z q stage hstage right coordinate))
            (tensorPowerBasis
              (EuclideanSpace.basisFun
                (Qubit.Bitstring (PhysicalSite m w)) Complex)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)
              (decodedRetryPoolSuccessorPortTrialHistory
                m w z q stage hstage left coordinate))) •
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)
            (decodedRetryPoolSuccessorPortTrialHistory
              m w z q stage hstage left branch))
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)
            (decodedRetryPoolSuccessorPortTrialHistory
              m w z q stage hstage right branch))).toLinearMap := by sorry
