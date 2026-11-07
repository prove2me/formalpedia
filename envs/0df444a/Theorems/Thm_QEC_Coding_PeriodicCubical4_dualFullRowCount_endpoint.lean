-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualFullRowCount_endpoint
-- name    : QEC.Coding.PeriodicCubical4.dualFullRowCount_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:44:57.195201+00:00
-- url     : https://prove2.me/theorems/2819e5e8-e962-49aa-a578-c76449b99e72
-- title:
--   Periodic Cubical4: dual Full Row Count endpoint
-- statement:
--   The Periodic Cubical4 construction uses the dual Full Row Count endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1410-L1417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1410-L1417

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualFullRowCount_endpoint
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    dualFullRowCount γ γ.increments.length = L := by sorry
