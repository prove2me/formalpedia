-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
-- name    : QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:43:46.058509+00:00
-- url     : https://prove2.me/theorems/0da61f08-86e5-4ec9-b099-b81d273dab22
-- title:
--   Finite Instrument: mem tensor Power Accepted Indices
-- statement:
--   The Finite Instrument construction uses the mem tensor Power Accepted Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L87-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L87-L92

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (trial : Fin attempts) :
    trial ∈ tensorPowerAcceptedIndices accepts attempts history ↔
      accepts (tensorPowerHistoryAt α attempts history trial) := by sorry
