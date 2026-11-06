-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelector_ne_of_ne
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_ne_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:35.849017+00:00
-- url     : https://prove2.me/theorems/bc298338-ba86-49ca-a0c5-94b8ecc88d57
-- title:
--   Finite Instrument: tensor Power Accepted Selector ne of ne
-- statement:
--   The Finite Instrument construction uses the tensor Power Accepted Selector ne of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L147-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L147-L153

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_ne_of_ne {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    {first second : Fin required} (hne : first ≠ second) :
    tensorPowerAcceptedSelector accepts attempts history required hrequired first ≠
      tensorPowerAcceptedSelector accepts attempts history required hrequired second := by sorry
