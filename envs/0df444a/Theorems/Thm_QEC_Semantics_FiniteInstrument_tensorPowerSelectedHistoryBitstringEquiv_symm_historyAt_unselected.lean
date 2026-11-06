-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:32:44.228243+00:00
-- url     : https://prove2.me/theorems/e10b25f5-85af-4600-8e2e-ce456f021abf
-- title:
--   Finite Instrument: tensor Power Selected History Bitstring Equiv symm history At unselected
-- statement:
--   Reconstructing a full history from selected/complement labels reads the
--   whole corresponding local complement bitstring on every unselected trial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean#L369-L388
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean#L369-L388

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
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
    (trial : tensorPowerUnselectedTrial accepts attempts history required hrequired) :
    tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history required
          hrequired ι).symm (selected, complement)) trial.1 =
      tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts history
        required hrequired ι complement trial := by sorry
