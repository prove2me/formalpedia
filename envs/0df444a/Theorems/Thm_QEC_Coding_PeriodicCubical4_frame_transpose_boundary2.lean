-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_frame_transpose_boundary2
-- name    : QEC.Coding.PeriodicCubical4.frame_transpose_boundary2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:23:18.914983+00:00
-- url     : https://prove2.me/theorems/24980545-ad69-47f3-9e10-82837d22da15
-- title:
--   Periodic Cubical4: frame transpose boundary2
-- statement:
--   The transpose plaquette coboundary is equivariant under coordinate frames.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L326-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L326-L351

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.frame_transpose_boundary2 {L : Nat} [NeZero L]
    (p : Plane) (e : Word (ZMod 2) (Link L)) :
    framePlaquetteWord p (wordLinearMapTranspose boundary2 e) =
      wordLinearMapTranspose boundary2 (frameLinkWord p e) := by sorry
