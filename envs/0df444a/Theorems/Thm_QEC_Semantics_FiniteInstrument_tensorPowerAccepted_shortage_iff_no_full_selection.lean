-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAccepted_shortage_iff_no_full_selection
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerAccepted_shortage_iff_no_full_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:37.433874+00:00
-- url     : https://prove2.me/theorems/048aec4f-1a83-46cd-a4e6-09f18af83c37
-- title:
--   Finite Instrument: tensor Power Accepted shortage iff no full selection
-- statement:
--   The finite shortage condition is exactly the absence of any injective full
--   selection whose trial indices are all accepted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L184-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L184-L212

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerAccepted_shortage_iff_no_full_selection {α : Type v}
    (accepts : α → Prop) [DecidablePred accepts] (attempts : Nat)
    (history : tensorPowerHistory α attempts) (required : Nat) :
    (tensorPowerAcceptedIndices accepts attempts history).card < required ↔
      ¬ ∃ selection : Fin required → Fin attempts,
        Function.Injective selection ∧
          ∀ slot, selection slot ∈ tensorPowerAcceptedIndices accepts attempts history := by sorry
