-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_dualMembrane
-- name    : QEC.Coding.PeriodicCubical4.btExcessEnergy_dualMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:24:51.072754+00:00
-- url     : https://prove2.me/theorems/5799807e-f449-4140-8e76-58d09870938a
-- title:
--   Periodic Cubical4: bt Excess Energy dual Membrane
-- statement:
--   BT09 excess energy is twice the dual DKLP loop length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L193-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L193-L197

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.btExcessEnergy_dualMembrane (m : PartialDualMembrane (L := L)) :
    (toricHamiltonian (L := L)).btExcessEnergy (dualMembraneError m) =
      2 * dualLoopLength m := by sorry
