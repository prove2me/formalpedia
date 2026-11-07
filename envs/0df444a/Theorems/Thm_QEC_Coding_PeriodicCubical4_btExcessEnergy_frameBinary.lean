-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_frameBinary
-- name    : QEC.Coding.PeriodicCubical4.btExcessEnergy_frameBinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:29:41.916053+00:00
-- url     : https://prove2.me/theorems/331bc03d-f74f-4cf5-8cee-b4d7852fe0ed
-- title:
--   Periodic Cubical4: bt Excess Energy frame Binary
-- statement:
--   BT excess energy is invariant under coordinate framing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L510-L532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L510-L532

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.btExcessEnergy_frameBinary {L : Nat} [NeZero L] [Fact (1 < L)]
    (p : Plane) (E : Binary (Plaquette L)) :
    (toricHamiltonian (L := L)).btExcessEnergy (frameBinary p E) =
      (toricHamiltonian (L := L)).btExcessEnergy E := by sorry
