-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_exists_dual_large_defect_loop
-- name    : QEC.Coding.PeriodicCubical4.exists_dual_large_defect_loop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:46:25.337556+00:00
-- url     : https://prove2.me/theorems/c3eadd66-cc04-43a2-88fa-1262ebd1e55b
-- title:
--   Periodic Cubical4: exists dual large defect loop
-- statement:
--   Every path to the dual sector crosses a state whose actual dual
--   defect-loop length is linear in `L`, with the same explicit constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1483-L1496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1483-L1496

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.exists_dual_large_defect_loop
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    ∃ n ≤ γ.increments.length,
      L / 2 ≤ 2 * dualLoopLength (γ.stateAt n).vector.xPart := by sorry
