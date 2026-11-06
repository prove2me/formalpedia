-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_symm_at_selected
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_symm_at_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:32:33.725456+00:00
-- url     : https://prove2.me/theorems/8a5dfac9-bab0-4dea-93d9-3871e36fbf0d
-- title:
--   Finite Instrument: tensor Power Selected History Bitstring Equiv symm at selected
-- statement:
--   Reconstructing a full history from selected/complement labels reads the
--   selected label on every actual selector image trial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean#L289-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean#L289-L313

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialComplement
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_symm_at_selected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired
        ι).ComplementCoordinates)
    (slot : Fin required) (port : ι) :
    tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history required
          hrequired ι).symm (selected, complement))
        (tensorPowerAcceptedSelector accepts attempts history required hrequired slot)
        port =
      selected (slot, port) := by sorry
