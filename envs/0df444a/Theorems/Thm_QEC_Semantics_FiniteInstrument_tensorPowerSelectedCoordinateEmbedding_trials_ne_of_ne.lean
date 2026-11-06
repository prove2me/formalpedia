-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedCoordinateEmbedding_trials_ne_of_ne
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedCoordinateEmbedding_trials_ne_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:33:59.746625+00:00
-- url     : https://prove2.me/theorems/d295e236-9a45-45b1-8464-f2b8128ce780
-- title:
--   Finite Instrument: tensor Power Selected Coordinate Embedding trials ne of ne
-- statement:
--   Distinct requested selected slots map to distinct actual trial indices,
--   at every common local port.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystem.lean#L156-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystem.lean#L156-L169

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedCoordinateEmbedding_trials_ne_of_ne
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {first second : Fin required} (hne : first ≠ second) (port : ι) :
    (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
      (first, port)).1 ≠
      (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
        (second, port)).1 := by sorry
