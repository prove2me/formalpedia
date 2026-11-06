-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelector_satisfies
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_satisfies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:33:38.607679+00:00
-- url     : https://prove2.me/theorems/f47a2686-ca5a-4f85-85a2-3fd54e936ee7
-- title:
--   Finite Instrument: tensor Power Accepted Selector satisfies
-- statement:
--   The Finite Instrument construction uses the tensor Power Accepted Selector satisfies property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L131-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L131-L139

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_satisfies {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (slot : Fin required) :
    accepts
      (tensorPowerHistoryAt α attempts history
        (tensorPowerAcceptedSelector accepts attempts history required hrequired slot)) := by sorry
