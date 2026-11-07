-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_two_mul_primalLoopLength_le_btExcessEnergy
-- name    : QEC.Coding.PeriodicCubical4.two_mul_primalLoopLength_le_btExcessEnergy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:36:49.485188+00:00
-- url     : https://prove2.me/theorems/ce84761b-95d7-4da0-a9fb-5cb5aa5e56d6
-- title:
--   Periodic Cubical4: two mul primal Loop Length le bt Excess Energy
-- statement:
--   The full Pauli energy dominates twice the primal loop length of its Z
--   component, even when an X component is also present.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1272-L1281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1272-L1281

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.two_mul_primalLoopLength_le_btExcessEnergy
    (E : Binary (Plaquette L)) :
    2 * primalLoopLength E.vector.zPart ≤
      (toricHamiltonian (L := L)).btExcessEnergy E := by sorry
