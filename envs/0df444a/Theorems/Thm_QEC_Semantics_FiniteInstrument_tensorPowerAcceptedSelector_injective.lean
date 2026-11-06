-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelector_injective
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:09:14.20107+00:00
-- url     : https://prove2.me/theorems/7ff93ebc-2425-4b70-8c92-9d0bb134dba9
-- title:
--   Finite Instrument: tensor Power Accepted Selector injective
-- statement:
--   The Finite Instrument construction uses the tensor Power Accepted Selector injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L141-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L141-L145

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_injective {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card) :
    Function.Injective (tensorPowerAcceptedSelector accepts attempts history required hrequired) := by sorry
