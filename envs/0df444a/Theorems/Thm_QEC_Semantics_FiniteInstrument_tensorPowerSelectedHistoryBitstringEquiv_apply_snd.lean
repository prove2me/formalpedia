-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:14.302734+00:00
-- url     : https://prove2.me/theorems/59c9b770-bb73-4681-898b-6f53ecba3326
-- title:
--   Finite Instrument: tensor Power Selected History Bitstring Equiv apply snd
-- statement:
--   The discarded component of the full selected/complement history
--   equivalence is the previously exposed complement bitstring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L100-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean#L100-L112

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    (tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
      required hrequired ι basisHistory).2 =
        tensorPowerSelectedComplementBitstring accepts attempts observedHistory required
          hrequired ι basisHistory := by sorry

attribute [defeq] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
