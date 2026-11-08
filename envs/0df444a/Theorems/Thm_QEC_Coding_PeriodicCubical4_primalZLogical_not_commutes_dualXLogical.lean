-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalZLogical_not_commutes_dualXLogical
-- name    : QEC.Coding.PeriodicCubical4.primalZLogical_not_commutes_dualXLogical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:49:20.852507+00:00
-- url     : https://prove2.me/theorems/cf91b03d-dc38-498a-81ac-eaddf935aac2
-- title:
--   Periodic Cubical4: primal ZLogical not commutes dual XLogical
-- statement:
--   The paired primal-Z and dual-X logical Paulis anticommute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L476-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L476-L489

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic

theorem QEC.Coding.PeriodicCubical4.primalZLogical_not_commutes_dualXLogical {L : Nat} [NeZero L]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    ¬ Commutes (primalZLogical z₀ w₀) (dualXLogical x₀ y₀) := by sorry
