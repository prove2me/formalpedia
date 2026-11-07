-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_exists_dual_half_filled_state
-- name    : QEC.Coding.PeriodicCubical4.exists_dual_half_filled_state
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:45:29.192585+00:00
-- url     : https://prove2.me/theorems/8ccb85ef-8904-4726-aafb-60f12e870ff8
-- title:
--   Periodic Cubical4: exists dual half filled state
-- statement:
--   Every path to the dual membrane sector contains a state whose dual
--   projection has exactly half of its rows filled.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1451-L1461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1451-L1461

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.exists_dual_half_filled_state
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    ∃ n ≤ γ.increments.length, dualFullRowCount γ n = L / 2 := by sorry
