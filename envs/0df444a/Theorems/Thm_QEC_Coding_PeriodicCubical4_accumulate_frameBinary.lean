-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_accumulate_frameBinary
-- name    : QEC.Coding.PeriodicCubical4.accumulate_frameBinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:24:40.565376+00:00
-- url     : https://prove2.me/theorems/f2c5dc1c-2130-4554-9efe-2b0d33f458f7
-- title:
--   Periodic Cubical4: accumulate frame Binary
-- statement:
--   The Periodic Cubical4 construction uses the accumulate frame Binary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L550-L569
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L550-L569

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.accumulate_frameBinary {L : Nat} [NeZero L]
    (p : Plane) (steps : List (Binary (Plaquette L))) :
    PauliErrorPath.accumulate (steps.map (frameBinary p)) =
      frameBinary p (PauliErrorPath.accumulate steps) := by sorry
