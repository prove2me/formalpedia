-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalXYMembrane_not_mem_middleBoundaryCode
-- name    : QEC.Coding.PeriodicCubical4.primalXYMembrane_not_mem_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:12:11.489492+00:00
-- url     : https://prove2.me/theorems/3af83302-ac1a-4321-84c5-df8dd4bd3768
-- title:
--   Periodic Cubical4: primal XYMembrane not mem middle Boundary Code
-- statement:
--   Pairing with the dual cocycle proves the primal membrane is not a boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L235-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L235-L248

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators

theorem QEC.Coding.PeriodicCubical4.primalXYMembrane_not_mem_middleBoundaryCode {L : Nat} [NeZero L]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    primalXYMembrane z₀ w₀ ∉
      (plaquetteChainComplex (L := L)).middleBoundaryCode.carrier := by sorry
