-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_framePlaquetteWord_left
-- name    : QEC.Coding.PeriodicCubical4.wordPairing_framePlaquetteWord_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:24:24.458585+00:00
-- url     : https://prove2.me/theorems/8b9bf897-d7a2-42ca-8311-87cd4fbcc6c6
-- title:
--   Periodic Cubical4: word Pairing frame Plaquette Word left
-- statement:
--   Moving one framed argument across the pairing frames the other one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L312-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L312-L323

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.wordPairing_framePlaquetteWord_left {L : Nat} [NeZero L]
    (p : Plane) (x y : Word (ZMod 2) (Plaquette L)) :
    wordPairing (framePlaquetteWord p x) y =
      wordPairing x (framePlaquetteWord p y) := by sorry
