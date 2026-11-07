-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_dualCoordinate_primalCoordinate
-- name    : QEC.Coding.PeriodicCubical4.wordPairing_dualCoordinate_primalCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:26.176418+00:00
-- url     : https://prove2.me/theorems/5d85a533-0521-466f-ad8a-50f47b4a160f
-- title:
--   Periodic Cubical4: word Pairing dual Coordinate primal Coordinate
-- statement:
--   The six framed primal/dual membrane pairs have the Kronecker pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L636-L659
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L636-L659

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.wordPairing_dualCoordinate_primalCoordinate
    {L : Nat} [NeZero L]
    (p q : Plane) (a b c d : ZMod L) :
    wordPairing (dualCoordinateMembrane p a b)
      (primalCoordinateMembrane q c d) = if p = q then 1 else 0 := by sorry
