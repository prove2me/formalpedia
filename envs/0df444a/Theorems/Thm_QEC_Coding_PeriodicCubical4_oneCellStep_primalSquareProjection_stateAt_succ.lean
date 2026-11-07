-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_oneCellStep_primalSquareProjection_stateAt_succ
-- name    : QEC.Coding.PeriodicCubical4.oneCellStep_primalSquareProjection_stateAt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:43:35.831267+00:00
-- url     : https://prove2.me/theorems/b07786c3-00fa-47eb-862f-91166dca6fe1
-- title:
--   Periodic Cubical4: one Cell Step primal Square Projection state At succ
-- statement:
--   Consecutive path states differ by at most one cell in the primal square
--   projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1332-L1350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1332-L1350

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.oneCellStep_primalSquareProjection_stateAt_succ
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    BinarySquare.OneCellStep
      (primalSquareProjection (γ.stateAt (n + 1)).vector.zPart)
      (primalSquareProjection (γ.stateAt n).vector.zPart) := by sorry
