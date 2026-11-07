-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_HammingWeight_dualSquareProjection_cellWord_le_one
-- name    : QEC.Coding.PeriodicCubical4.HammingWeight_dualSquareProjection_cellWord_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:40:09.436283+00:00
-- url     : https://prove2.me/theorems/1ceae0af-cc72-4b60-8572-10681eb72473
-- title:
--   Periodic Cubical4: Hamming Weight dual Square Projection cell Word le one
-- statement:
--   A single plaquette changes at most one dual projected square cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L483-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L483-L490

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.HammingWeight_dualSquareProjection_cellWord_le_one (p : Plaquette L) :
    HammingWeight
        ((fun q : Fin L × Fin L =>
          dualSquareProjection (L := L) (cellWord p) q.1 q.2) :
          Word (ZMod 2) (Fin L × Fin L)) ≤ 1 := by sorry
