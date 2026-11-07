-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_frame_boundary3
-- name    : QEC.Coding.PeriodicCubical4.frame_boundary3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:24:19.592278+00:00
-- url     : https://prove2.me/theorems/bfee77f8-7110-4be5-8ef3-608b7a791f7e
-- title:
--   Periodic Cubical4: frame boundary3
-- statement:
--   Coordinate relabeling commutes with the cube-to-plaquette boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L293-L300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L293-L300

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.frame_boundary3 {L : Nat} [NeZero L]
    (p : Plane) (m : Word (ZMod 2) (Cube L)) :
    framePlaquetteWord p (boundary3 m) =
      boundary3 (frameCubeWord p m) := by sorry
