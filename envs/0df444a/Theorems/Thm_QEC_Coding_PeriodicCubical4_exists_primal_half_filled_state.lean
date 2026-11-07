-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_exists_primal_half_filled_state
-- name    : QEC.Coding.PeriodicCubical4.exists_primal_half_filled_state
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:44:37.457614+00:00
-- url     : https://prove2.me/theorems/02836cd6-2fb9-42b2-9ed7-524e94711fa1
-- title:
--   Periodic Cubical4: exists primal half filled state
-- statement:
--   Every path to the primal membrane sector contains a state whose primal
--   projection has exactly half of its rows filled.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1437-L1447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1437-L1447

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.exists_primal_half_filled_state
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ) :
    ∃ n ≤ γ.increments.length, primalFullRowCount γ n = L / 2 := by sorry
