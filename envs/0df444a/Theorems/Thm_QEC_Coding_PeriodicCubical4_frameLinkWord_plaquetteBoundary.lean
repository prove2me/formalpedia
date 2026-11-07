-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_frameLinkWord_plaquetteBoundary
-- name    : QEC.Coding.PeriodicCubical4.frameLinkWord_plaquetteBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:28:05.60647+00:00
-- url     : https://prove2.me/theorems/a2ce0d79-04e0-42b5-b9ca-84118054fe6d
-- title:
--   Periodic Cubical4: frame Link Word plaquette Boundary
-- statement:
--   Coordinate frames carry plaquette boundaries to plaquette boundaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L263-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L263-L270

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.frameLinkWord_plaquetteBoundary {L : Nat} [NeZero L]
    (p : Plane) (q : Plaquette L) :
    frameLinkWord p (plaquetteBoundary q) =
      plaquetteBoundary (framePlaquette p q) := by sorry
