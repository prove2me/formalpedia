-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalXYPureZLogicalClass_ne_zero
-- name    : QEC.Coding.PeriodicCubical4.primalXYPureZLogicalClass_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:44:04.384195+00:00
-- url     : https://prove2.me/theorems/bdf35828-3e9c-472c-8c7e-736201c4a5bc
-- title:
--   Periodic Cubical4: primal XYPure ZLogical Class ne zero
-- statement:
--   The Periodic Cubical4 construction uses the primal XYPure ZLogical Class ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L314-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L314-L319

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators

theorem QEC.Coding.PeriodicCubical4.primalXYPureZLogicalClass_ne_zero {L : Nat} [NeZero L]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    primalXYPureZLogicalClass z₀ w₀ ≠ 0 := by sorry
