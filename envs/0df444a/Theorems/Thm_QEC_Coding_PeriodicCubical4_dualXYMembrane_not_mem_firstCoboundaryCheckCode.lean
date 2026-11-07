-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualXYMembrane_not_mem_firstCoboundaryCheckCode
-- name    : QEC.Coding.PeriodicCubical4.dualXYMembrane_not_mem_firstCoboundaryCheckCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:12:23.097046+00:00
-- url     : https://prove2.me/theorems/d2ad14d5-0b15-4b91-9930-a4d786b57340
-- title:
--   Periodic Cubical4: dual XYMembrane not mem first Coboundary Check Code
-- statement:
--   Pairing with the primal cycle proves the dual membrane is not a coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L251-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L251-L265

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators

theorem QEC.Coding.PeriodicCubical4.dualXYMembrane_not_mem_firstCoboundaryCheckCode {L : Nat} [NeZero L]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    dualXYMembrane x₀ y₀ ∉
      (plaquetteChainComplex (L := L)).firstCoboundaryCheckCode.carrier := by sorry
