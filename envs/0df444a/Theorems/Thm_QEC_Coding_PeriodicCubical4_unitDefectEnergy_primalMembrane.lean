-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_unitDefectEnergy_primalMembrane
-- name    : QEC.Coding.PeriodicCubical4.unitDefectEnergy_primalMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:33:13.758813+00:00
-- url     : https://prove2.me/theorems/060cf9e2-b45f-4354-bae9-214935ed28ae
-- title:
--   Periodic Cubical4: unit Defect Energy primal Membrane
-- statement:
--   DKLP unit defect energy is exactly primal syndrome-loop length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L170-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L170-L175

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.unitDefectEnergy_primalMembrane (m : PartialPrimalMembrane (L := L)) :
    (toricHamiltonian (L := L)).unitDefectEnergy (primalMembraneError m) =
      primalLoopLength m := by sorry
