-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_frameBinary_binaryMul
-- name    : QEC.Coding.PeriodicCubical4.frameBinary_binaryMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:28:12.808522+00:00
-- url     : https://prove2.me/theorems/ae908ff3-8738-42f9-a1fa-5e4c66b49177
-- title:
--   Periodic Cubical4: frame Binary binary Mul
-- statement:
--   The Periodic Cubical4 construction uses the frame Binary binary Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L400-L416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L400-L416

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.frameBinary_binaryMul {L : Nat} [NeZero L]
    (p : Plane) (E F : Binary (Plaquette L)) :
    frameBinary p (binaryMul E F) =
      binaryMul (frameBinary p E) (frameBinary p F) := by sorry
