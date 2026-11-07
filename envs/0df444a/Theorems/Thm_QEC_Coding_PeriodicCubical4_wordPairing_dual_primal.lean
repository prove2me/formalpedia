-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_dual_primal
-- name    : QEC.Coding.PeriodicCubical4.wordPairing_dual_primal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:12:26.899382+00:00
-- url     : https://prove2.me/theorems/ae13ac7d-b5c5-4175-9bcb-fdc73dd214a1
-- title:
--   Periodic Cubical4: word Pairing dual primal
-- statement:
--   Paired primal and dual membranes meet in exactly one plaquette modulo two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L205-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L205-L218

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators

theorem QEC.Coding.PeriodicCubical4.wordPairing_dual_primal {L : Nat} [NeZero L]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    wordPairing (dualXYMembrane x₀ y₀) (primalXYMembrane z₀ w₀) = 1 := by sorry
