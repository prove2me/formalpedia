-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_symplecticForm_frameBinary
-- name    : QEC.Coding.PeriodicCubical4.symplecticForm_frameBinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:28:26.565925+00:00
-- url     : https://prove2.me/theorems/28f956b5-e642-4836-96d1-fedac59db6c3
-- title:
--   Periodic Cubical4: symplectic Form frame Binary
-- statement:
--   The symplectic form is invariant under simultaneous coordinate framing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L474-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L474-L482

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.symplecticForm_frameBinary {L : Nat} [NeZero L]
    (p : Plane) (E F : Binary (Plaquette L)) :
    symplecticForm (frameBinary p E).vector (frameBinary p F).vector =
      symplecticForm E.vector F.vector := by sorry
