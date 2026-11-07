-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_oneCellStep_dualSquareProjection_stateAt_succ
-- name    : QEC.Coding.PeriodicCubical4.oneCellStep_dualSquareProjection_stateAt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:45:58.528186+00:00
-- url     : https://prove2.me/theorems/a17c6867-491e-4e2c-8606-e1d5a7511bb3
-- title:
--   Periodic Cubical4: one Cell Step dual Square Projection state At succ
-- statement:
--   Consecutive path states differ by at most one cell in the dual square
--   projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1354-L1372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1354-L1372

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.oneCellStep_dualSquareProjection_stateAt_succ
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    BinarySquare.OneCellStep
      (dualSquareProjection (γ.stateAt (n + 1)).vector.xPart)
      (dualSquareProjection (γ.stateAt n).vector.xPart) := by sorry
