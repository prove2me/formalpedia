-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalFullRowCount_zero
-- name    : QEC.Coding.PeriodicCubical4.primalFullRowCount_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:28:52.67408+00:00
-- url     : https://prove2.me/theorems/0d6f9ae4-e44a-487a-afbf-1fd7910287ef
-- title:
--   Periodic Cubical4: primal Full Row Count zero
-- statement:
--   The Periodic Cubical4 construction uses the primal Full Row Count zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1387-L1392
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1387-L1392

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalFullRowCount_zero
    (γ : PauliErrorPath (ι := Plaquette L)) :
    primalFullRowCount γ 0 = 0 := by sorry
