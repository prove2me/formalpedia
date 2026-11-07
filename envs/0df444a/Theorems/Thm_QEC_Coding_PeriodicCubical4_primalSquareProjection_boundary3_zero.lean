-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSquareProjection_boundary3_zero
-- name    : QEC.Coding.PeriodicCubical4.primalSquareProjection_boundary3_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:29:38.669197+00:00
-- url     : https://prove2.me/theorems/fac610a0-41de-4741-91b2-be05ce7989de
-- title:
--   Periodic Cubical4: primal Square Projection boundary3 zero
-- statement:
--   The Periodic Cubical4 construction uses the primal Square Projection boundary3 zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L935-L942
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L935-L942

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalSquareProjection_boundary3_zero {L : Nat}
    [NeZero L] [Fact (1 < L)]
    (c : Word (ZMod 2) (Cube L)) :
    primalSquareProjection (boundary3 c) = (0 : BinarySquare.Grid L) := by sorry
