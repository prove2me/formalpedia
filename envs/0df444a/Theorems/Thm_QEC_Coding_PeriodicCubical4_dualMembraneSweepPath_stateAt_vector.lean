-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualMembraneSweepPath_stateAt_vector
-- name    : QEC.Coding.PeriodicCubical4.dualMembraneSweepPath_stateAt_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:50:31.160942+00:00
-- url     : https://prove2.me/theorems/a8e0c4c5-f076-4679-8366-4023cdc66980
-- title:
--   Periodic Cubical4: dual Membrane Sweep Path state At vector
-- statement:
--   During the geometric part of the dual sweep, the actual accumulated
--   Pauli vector is exactly the pure-X error of the concrete row-major prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L911-L931
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L911-L931

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualMembraneSweepPath_stateAt_vector
    (x y : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    ((dualMembraneSweepPath x y).stateAt n).vector =
      (dualMembraneError (dualSweepPrefix x y n)).vector := by sorry
