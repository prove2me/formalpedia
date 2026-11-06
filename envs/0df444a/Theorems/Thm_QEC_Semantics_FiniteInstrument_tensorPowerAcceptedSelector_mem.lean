-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelector_mem
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:08:59.039198+00:00
-- url     : https://prove2.me/theorems/fb97a3d0-217c-4a7d-b2cb-64a378bfa427
-- title:
--   Finite Instrument: tensor Power Accepted Selector mem
-- statement:
--   The Finite Instrument construction uses the tensor Power Accepted Selector mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L123-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L123-L129

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_mem {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (slot : Fin required) :
    tensorPowerAcceptedSelector accepts attempts history required hrequired slot ∈
      tensorPowerAcceptedIndices accepts attempts history := by sorry
