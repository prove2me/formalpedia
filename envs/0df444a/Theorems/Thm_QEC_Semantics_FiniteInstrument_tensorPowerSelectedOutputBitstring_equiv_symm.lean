-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedOutputBitstring_equiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:38.414928+00:00
-- url     : https://prove2.me/theorems/2d532f86-2ab4-45c9-baff-c31ad38d152b
-- title:
--   Finite Instrument: tensor Power Selected Output Bitstring equiv symm
-- statement:
--   Rebuilding an input history from a selected/complement pair recovers its
--   selected requested-slot label exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L116-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L116-L132

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedOutputBitstring_equiv_symm
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).ComplementCoordinates) :
    tensorPowerSelectedOutputBitstring accepts attempts observedHistory required
        hrequired ι
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
          required hrequired ι).symm (selected, complement)) = selected := by sorry
