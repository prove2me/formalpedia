-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_toricSyndrome_eq_componentDefectLoops
-- name    : QEC.Coding.PeriodicCubical4.toricSyndrome_eq_componentDefectLoops
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:30:32.320708+00:00
-- url     : https://prove2.me/theorems/0391922a-a8f0-4ee8-afe9-aff7f7212f57
-- title:
--   Periodic Cubical4: toric Syndrome eq component Defect Loops
-- statement:
--   The selected toric syndrome of an arbitrary Pauli splits into the primal
--   loop of its Z component and the dual loop of its X component.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1203-L1224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1203-L1224

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.toricSyndrome_eq_componentDefectLoops (E : Binary (Plaquette L)) :
    stabilizerSyndrome (toricGenerator (L := L)) E =
      Sum.elim (primalDefectLoop E.vector.zPart)
        (dualDefectLoop E.vector.xPart) := by sorry
