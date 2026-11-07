-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_hasDualMembraneEndpoint
-- name    : QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasDualMembraneEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:45:52.777072+00:00
-- url     : https://prove2.me/theorems/2b6e3f5c-651d-492e-8a25-b1108727edf5
-- title:
--   Periodic Cubical4: half le path Height of has Dual Membrane Endpoint
-- statement:
--   Explicit linear BT09 path-height lower bound for the dual membrane
--   sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1512-L1520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1512-L1520

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasDualMembraneEndpoint
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ := by sorry
