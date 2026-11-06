-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedComplementBitstring_equiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:56.790971+00:00
-- url     : https://prove2.me/theorems/166aa948-fba4-4c83-acba-80e9ceaac360
-- title:
--   Finite Instrument: tensor Power Selected Complement Bitstring equiv symm
-- statement:
--   Rebuilding an input history from a selected/complement pair recovers its
--   discarded complement label exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L136-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L136-L152

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedComplementBitstring_equiv_symm
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
    tensorPowerSelectedComplementBitstring accepts attempts observedHistory required
        hrequired ι
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
          required hrequired ι).symm (selected, complement)) = complement := by sorry
