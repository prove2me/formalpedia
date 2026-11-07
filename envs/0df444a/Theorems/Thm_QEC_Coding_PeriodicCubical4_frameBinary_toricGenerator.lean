-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_frameBinary_toricGenerator
-- name    : QEC.Coding.PeriodicCubical4.frameBinary_toricGenerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:28:23.983318+00:00
-- url     : https://prove2.me/theorems/94c07c99-29ad-4483-befb-f0db37464d1e
-- title:
--   Periodic Cubical4: frame Binary toric Generator
-- statement:
--   Coordinate frames carry every selected toric generator to the relabeled one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L459-L471
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L459-L471

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.frameBinary_toricGenerator {L : Nat} [NeZero L] [Fact (1 < L)]
    (p : Plane) (j : Sum (Link L) (Cube L)) :
    frameBinary p (toricGenerator (L := L) j) =
      toricGenerator (frameGeneratorIndex p j) := by sorry
