-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_matrixEntry
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:49.392272+00:00
-- url     : https://prove2.me/theorems/e59a0c09-30a2-479c-9670-d29213d16cf4
-- title:
--   Finite Instrument: tensor Power Selected Partial Trace Channel matrix Entry
-- statement:
--   A requested-slot matrix entry of the selected output is the sum of input
--   matrix entries with the same literal discarded-complement label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L327-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L327-L437

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_matrixEntry
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι A
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex right)) =
      ∑ complement : Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates,
        inner Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
              required hrequired ι).symm (left, complement)))
          (A
            (tensorPowerBasis
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
              ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
                required hrequired ι).symm (right, complement)))) := by sorry
