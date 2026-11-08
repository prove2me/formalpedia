-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_fourDimensionalToric_membranePath_linearEnergyBarrier
-- name    : QEC.Coding.PeriodicCubical4.fourDimensionalToric_membranePath_linearEnergyBarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:53:01.826259+00:00
-- url     : https://prove2.me/theorems/31db2f29-63ed-4a4e-9a49-195a3c3568d4
-- title:
--   Periodic Cubical4: four Dimensional Toric membrane Path linear Energy Barrier
-- statement:
--   The fully proved finite lower-bound theorem for both chosen nontrivial
--   membrane sectors of the periodic four-dimensional toric code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1524-L1530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1524-L1530

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.fourDimensionalToric_membranePath_linearEnergyBarrier
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ ∨ HasDualMembraneEndpoint γ) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ := by sorry
