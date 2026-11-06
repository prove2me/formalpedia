-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelectorOption_eq_none_iff
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelectorOption_eq_none_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:33:23.930203+00:00
-- url     : https://prove2.me/theorems/4c3ef1ed-2c6a-42e1-8caf-e347cec2f0b8
-- title:
--   Finite Instrument: tensor Power Accepted Selector Option eq none iff
-- statement:
--   The Finite Instrument construction uses the tensor Power Accepted Selector Option eq none iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L167-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L167-L178

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelectorOption_eq_none_iff {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) :
    tensorPowerAcceptedSelectorOption accepts attempts history required = none ↔
      (tensorPowerAcceptedIndices accepts attempts history).card < required := by sorry
