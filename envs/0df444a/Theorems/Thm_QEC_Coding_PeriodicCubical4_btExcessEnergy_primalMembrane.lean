-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_primalMembrane
-- name    : QEC.Coding.PeriodicCubical4.btExcessEnergy_primalMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:24:40.483209+00:00
-- url     : https://prove2.me/theorems/8921f439-5af4-4bca-b3b7-2af745127ece
-- title:
--   Periodic Cubical4: bt Excess Energy primal Membrane
-- statement:
--   BT09 excess energy is twice the primal DKLP loop length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L186-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L186-L190

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.btExcessEnergy_primalMembrane (m : PartialPrimalMembrane (L := L)) :
    (toricHamiltonian (L := L)).btExcessEnergy (primalMembraneError m) =
      2 * primalLoopLength m := by sorry
