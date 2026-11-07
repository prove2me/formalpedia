-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_frame_boundary2
-- name    : QEC.Coding.PeriodicCubical4.frame_boundary2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:28:19.351401+00:00
-- url     : https://prove2.me/theorems/859066e6-3c82-4ec8-96c8-76e71c360c11
-- title:
--   Periodic Cubical4: frame boundary2
-- statement:
--   Coordinate relabeling commutes with the plaquette-to-link boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L283-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L283-L290

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.frame_boundary2 {L : Nat} [NeZero L]
    (p : Plane) (m : Word (ZMod 2) (Plaquette L)) :
    frameLinkWord p (boundary2 m) =
      boundary2 (framePlaquetteWord p m) := by sorry
