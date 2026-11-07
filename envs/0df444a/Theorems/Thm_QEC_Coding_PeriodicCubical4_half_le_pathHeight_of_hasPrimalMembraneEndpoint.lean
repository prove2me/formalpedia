-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_hasPrimalMembraneEndpoint
-- name    : QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasPrimalMembraneEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:46:55.268893+00:00
-- url     : https://prove2.me/theorems/7e633d21-d82a-41d4-936f-399c6dac95cb
-- title:
--   Periodic Cubical4: half le path Height of has Primal Membrane Endpoint
-- statement:
--   Explicit linear BT09 path-height lower bound for the primal membrane
--   sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1500-L1508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1500-L1508

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasPrimalMembraneEndpoint
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ := by sorry
