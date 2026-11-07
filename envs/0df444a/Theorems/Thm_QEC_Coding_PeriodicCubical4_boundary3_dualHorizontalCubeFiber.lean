-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary3_dualHorizontalCubeFiber
-- name    : QEC.Coding.PeriodicCubical4.boundary3_dualHorizontalCubeFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:42:39.965189+00:00
-- url     : https://prove2.me/theorems/6364a386-f19f-41f2-82c2-068e39989685
-- title:
--   Periodic Cubical4: boundary3 dual Horizontal Cube Fiber
-- statement:
--   An `xyz` cube fiber fills precisely the gap between two adjacent primal
--   membrane slices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1016-L1037
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1016-L1037

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.boundary3_dualHorizontalCubeFiber (z w : ZMod L) :
    boundary3 (dualHorizontalCubeFiber z w) =
      primalXYMembrane z w + primalXYMembrane (z + 1) w := by sorry
