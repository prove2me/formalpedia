-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_oneCellStep_dualSquareProjection_of_HammingWeight_le_one
-- name    : QEC.Coding.PeriodicCubical4.oneCellStep_dualSquareProjection_of_HammingWeight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:40:02.51353+00:00
-- url     : https://prove2.me/theorems/cc3f626c-50a1-49e7-a2d8-86a51e2d1e34
-- title:
--   Periodic Cubical4: one Cell Step dual Square Projection of Hamming Weight le one
-- statement:
--   Any weight-at-most-one plaquette word changes at most one dual projected
--   cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L555-L573
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L555-L573

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.oneCellStep_dualSquareProjection_of_HammingWeight_le_one
    (m : Word (ZMod 2) (Plaquette L)) (hm : HammingWeight m ≤ 1) :
    BinarySquare.OneCellStep (dualSquareProjection m) 0 := by sorry
