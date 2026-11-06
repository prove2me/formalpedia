-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:25.47111+00:00
-- url     : https://prove2.me/theorems/ef57f443-c25f-483f-a5fb-d266f75dc2be
-- title:
--   Finite Instrument: tensor Power Selected History Bitstring Equiv apply fst
-- statement:
--   The retained component of the full selected/complement history equivalence
--   is the previously exposed requested-slot bitstring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L84-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L84-L96

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    (tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
      required hrequired ι basisHistory).1 =
        tensorPowerSelectedOutputBitstring accepts attempts observedHistory required
          hrequired ι basisHistory := by sorry

attribute [defeq] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
