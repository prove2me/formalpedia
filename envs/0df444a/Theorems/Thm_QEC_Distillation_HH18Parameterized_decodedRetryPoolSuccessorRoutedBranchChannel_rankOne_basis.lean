-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRoutedBranchChannel_rankOne_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:55:20.542541+00:00
-- url     : https://prove2.me/theorems/f09a1ec9-85d5-4e44-adf8-2e02e11162ba
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Routed Branch Channel rank One basis
-- statement:
--   On a source computational matrix unit, the routed successor selector
--   retains precisely the fixed logical port across all selected parent blocks;
--   all other logical ports contribute only their exact discarded-basis inner
--   products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L442-L514
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L442-L514

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
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
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (branch : Fin (logicalOutputCount m w))
    (left right : Qubit.Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorRoutedBranchChannel
        m w z q stage hstage branch
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorSourceSlots m w z q stage))
            Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorSourceSlots m w z q stage))
            Complex right)).toLinearMap =
      (∏ coordinate : Fin (logicalOutputCount m w),
          if coordinate = branch then 1
          else inner Complex
            (tensorPowerBasis
              (EuclideanSpace.basisFun
                (Qubit.Bitstring (PhysicalSite m w)) Complex)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)
              ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
                (decodedRetryPoolBackwardAttempts m w z q
                  ⟨stage.1 + 1, hstage⟩)).symm
                (fun target => right
                  ((decodedRetryPoolSuccessorAttemptSlotsEquiv
                    m w z q stage hstage).symm target,
                    (decodedRetryPoolLogicalSiteFinEquiv m w).symm coordinate))))
            (tensorPowerBasis
              (EuclideanSpace.basisFun
                (Qubit.Bitstring (PhysicalSite m w)) Complex)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)
              ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
                (decodedRetryPoolBackwardAttempts m w z q
                  ⟨stage.1 + 1, hstage⟩)).symm
                (fun target => left
                  ((decodedRetryPoolSuccessorAttemptSlotsEquiv
                    m w z q stage hstage).symm target,
                    (decodedRetryPoolLogicalSiteFinEquiv m w).symm coordinate))))) •
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)
            ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)).symm
              (fun target => left
                ((decodedRetryPoolSuccessorAttemptSlotsEquiv
                  m w z q stage hstage).symm target,
                  (decodedRetryPoolLogicalSiteFinEquiv m w).symm branch))))
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)
            ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)).symm
              (fun target => right
                ((decodedRetryPoolSuccessorAttemptSlotsEquiv
                  m w z q stage hstage).symm target,
                  (decodedRetryPoolLogicalSiteFinEquiv m w).symm branch))))).toLinearMap := by sorry
