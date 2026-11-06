-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_matrixUnitExpansion
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_matrixUnitExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:48.13619+00:00
-- url     : https://prove2.me/theorems/fdf98ec7-d284-49ff-a89e-0b2e8913289e
-- title:
--   Finite Instrument: tensor Power Selected Partial Trace Channel matrix Unit Expansion
-- statement:
--   Expand the actual selected-subsystem output in requested-slot matrix
--   units.  The only surviving coherence factor is the exact inner product of the
--   discarded complementary computational basis vectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L230-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L230-L323

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_matrixUnitExpansion
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)) :
    tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
        required hrequired ι A =
      ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
        ∑ left : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          (inner Complex
              (tensorPowerBasis
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
                attempts left)
              (A
                (tensorPowerBasis
                  (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
                  attempts right)) *
            inner Complex
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
