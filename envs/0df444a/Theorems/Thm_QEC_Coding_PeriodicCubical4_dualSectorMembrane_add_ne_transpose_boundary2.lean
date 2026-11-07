-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSectorMembrane_add_ne_transpose_boundary2
-- name    : QEC.Coding.PeriodicCubical4.dualSectorMembrane_add_ne_transpose_boundary2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:04:06.829132+00:00
-- url     : https://prove2.me/theorems/3f8c1aef-a655-4cc5-9f5e-fea5e459d173
-- title:
--   Periodic Cubical4: dual Sector Membrane add ne transpose boundary2
-- statement:
--   Distinct dual coefficient vectors remain distinct modulo coboundaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L871-L908
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L871-L908

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.dualSectorMembrane_add_ne_transpose_boundary2
    {L : Nat} [NeZero L] (s t : MembraneSector) (hst : s ≠ t)
    (e : Word (ZMod 2) (Link L)) :
    dualSectorMembrane s + dualSectorMembrane t ≠
      wordLinearMapTranspose boundary2 e := by sorry
