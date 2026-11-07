-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalMembraneSweepPath_stateAt_vector
-- name    : QEC.Coding.PeriodicCubical4.primalMembraneSweepPath_stateAt_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:50:27.280674+00:00
-- url     : https://prove2.me/theorems/0e1ac1aa-a71d-41d3-931d-e92a107804ff
-- title:
--   Periodic Cubical4: primal Membrane Sweep Path state At vector
-- statement:
--   During the geometric part of the primal sweep, the actual accumulated
--   Pauli vector is exactly the pure-Z error of the concrete row-major prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L887-L907
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L887-L907

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalMembraneSweepPath_stateAt_vector
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    ((primalMembraneSweepPath z w).stateAt n).vector =
      (primalMembraneError (primalSweepPrefix z w n)).vector := by sorry
