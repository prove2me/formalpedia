-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_rankOne_basis
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:56.979197+00:00
-- url     : https://prove2.me/theorems/6c2ac6c3-1ff0-4bd4-9184-ce778abb0821
-- title:
--   Finite Instrument: tensor Power Selected Partial Trace Channel rank One basis
-- statement:
--   On a computational matrix unit, the actual selected-subsystem channel
--   retains the reindexed selected matrix unit and multiplies it by the exact
--   inner product of the discarded complementary basis vectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L157-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L157-L225

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_rankOne_basis
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (left right : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
        required hrequired ι
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
            attempts left)
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
            attempts right)).toLinearMap =
      (inner Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (tensorPowerSelectedSubsystem accepts attempts observedHistory
                required hrequired ι).ComplementCoordinates)
            Complex
            (tensorPowerSelectedComplementBitstring accepts attempts
              observedHistory required hrequired ι right))
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (tensorPowerSelectedSubsystem accepts attempts observedHistory
                required hrequired ι).ComplementCoordinates)
            Complex
            (tensorPowerSelectedComplementBitstring accepts attempts
              observedHistory required hrequired ι left))) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι left))
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι right))).toLinearMap := by sorry
