-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSectorMembrane_add_ne_boundary3
-- name    : QEC.Coding.PeriodicCubical4.primalSectorMembrane_add_ne_boundary3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:03:41.949202+00:00
-- url     : https://prove2.me/theorems/380d7524-47ae-4b01-acc2-0854acf58271
-- title:
--   Periodic Cubical4: primal Sector Membrane add ne boundary3
-- statement:
--   Distinct primal coefficient vectors remain distinct modulo boundaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L844-L868
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L844-L868

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalSectorMembrane_add_ne_boundary3
    {L : Nat} [NeZero L] (s t : MembraneSector) (hst : s ≠ t)
    (c : Word (ZMod 2) (Cube L)) :
    primalSectorMembrane s + primalSectorMembrane t ≠ boundary3 c := by sorry
