-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualFullRowCount_zero
-- name    : QEC.Coding.PeriodicCubical4.dualFullRowCount_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:27:54.286006+00:00
-- url     : https://prove2.me/theorems/1ec71260-d197-428a-9e3c-1f3be0751607
-- title:
--   Periodic Cubical4: dual Full Row Count zero
-- statement:
--   The Periodic Cubical4 construction uses the dual Full Row Count zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1394-L1399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1394-L1399

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualFullRowCount_zero
    (γ : PauliErrorPath (ι := Plaquette L)) :
    dualFullRowCount γ 0 = 0 := by sorry
