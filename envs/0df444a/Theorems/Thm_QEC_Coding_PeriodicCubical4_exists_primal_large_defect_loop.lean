-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_exists_primal_large_defect_loop
-- name    : QEC.Coding.PeriodicCubical4.exists_primal_large_defect_loop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:45:49.150915+00:00
-- url     : https://prove2.me/theorems/28c353ce-13e8-4e85-91b7-237dd6289852
-- title:
--   Periodic Cubical4: exists primal large defect loop
-- statement:
--   Every path to the primal sector crosses a state whose actual primal
--   defect-loop length is linear in `L`, with the explicit finite-size constant
--   `L / 2 ≤ 2 * loopLength`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1466-L1479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1466-L1479

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.exists_primal_large_defect_loop
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ) :
    ∃ n ≤ γ.increments.length,
      L / 2 ≤ 2 * primalLoopLength (γ.stateAt n).vector.zPart := by sorry
