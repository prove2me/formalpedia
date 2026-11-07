-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_framePlaquetteWord
-- name    : QEC.Coding.PeriodicCubical4.wordPairing_framePlaquetteWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:23:15.578977+00:00
-- url     : https://prove2.me/theorems/fa7db481-503a-4d52-ba5f-44af8cde0b43
-- title:
--   Periodic Cubical4: word Pairing frame Plaquette Word
-- statement:
--   Reindexing both arguments by the same frame preserves the word pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L303-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L303-L309

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.wordPairing_framePlaquetteWord {L : Nat} [NeZero L]
    (p : Plane) (x y : Word (ZMod 2) (Plaquette L)) :
    wordPairing (framePlaquetteWord p x) (framePlaquetteWord p y) =
      wordPairing x y := by sorry
