-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_framePath
-- name    : QEC.Coding.PeriodicCubical4.pathHeight_framePath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:22:20.90527+00:00
-- url     : https://prove2.me/theorems/26a21307-e25a-42b4-9cf0-a7d5b9157775
-- title:
--   Periodic Cubical4: path Height frame Path
-- statement:
--   Path height is invariant under coordinate framing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L586-L594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L586-L594

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.pathHeight_framePath {L : Nat} [NeZero L] [Fact (1 < L)]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) :
    (toricHamiltonian (L := L)).pathHeight (framePath p gamma) =
      (toricHamiltonian (L := L)).pathHeight gamma := by sorry
