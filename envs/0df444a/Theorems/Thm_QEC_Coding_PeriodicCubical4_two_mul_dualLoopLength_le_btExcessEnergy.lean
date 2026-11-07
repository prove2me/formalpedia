-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_two_mul_dualLoopLength_le_btExcessEnergy
-- name    : QEC.Coding.PeriodicCubical4.two_mul_dualLoopLength_le_btExcessEnergy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:38:06.321966+00:00
-- url     : https://prove2.me/theorems/d18b45e0-d289-4b0b-87fa-f54e9d76645e
-- title:
--   Periodic Cubical4: two mul dual Loop Length le bt Excess Energy
-- statement:
--   The full Pauli energy dominates twice the dual loop length of its X
--   component, even when a Z component is also present.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1285-L1294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1285-L1294

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.two_mul_dualLoopLength_le_btExcessEnergy
    (E : Binary (Plaquette L)) :
    2 * dualLoopLength E.vector.xPart ≤
      (toricHamiltonian (L := L)).btExcessEnergy E := by sorry
