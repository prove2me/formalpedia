-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupChannel_rankOne_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:53:57.632286+00:00
-- url     : https://prove2.me/theorems/ffa4a334-c8b5-4f9b-84bd-53d044ce0276
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Regroup Channel rank One basis
-- statement:
--   Regrouping sends a flat computational matrix unit to the corresponding
--   nested computational matrix unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L245-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L245-L321

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (left right : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) :
    decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
            Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
            Complex right)).toLinearMap =
      (InnerProductSpace.rankOne Complex
        (tensorPowerBasis
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩))
          (logicalOutputCount m w)
          (decodedRetryPoolSuccessorRegroupBitstringEquiv
            m w z q stage hstage left))
        (tensorPowerBasis
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩))
          (logicalOutputCount m w)
          (decodedRetryPoolSuccessorRegroupBitstringEquiv
            m w z q stage hstage right))).toLinearMap := by sorry
