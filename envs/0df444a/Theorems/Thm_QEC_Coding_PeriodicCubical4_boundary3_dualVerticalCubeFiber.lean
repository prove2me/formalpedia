-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary3_dualVerticalCubeFiber
-- name    : QEC.Coding.PeriodicCubical4.boundary3_dualVerticalCubeFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:43:21.595291+00:00
-- url     : https://prove2.me/theorems/99aec5af-b4c4-4589-a2f6-b6f2f8210bc4
-- title:
--   Periodic Cubical4: boundary3 dual Vertical Cube Fiber
-- statement:
--   An `xyw` cube fiber fills precisely the gap between two adjacent primal
--   membrane slices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1041-L1062
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1041-L1062

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.boundary3_dualVerticalCubeFiber (z w : ZMod L) :
    boundary3 (dualVerticalCubeFiber z w) =
      primalXYMembrane z w + primalXYMembrane z (w + 1) := by sorry
