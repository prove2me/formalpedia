-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_toricSyndrome_dualMembrane
-- name    : QEC.Coding.PeriodicCubical4.toricSyndrome_dualMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:34:57.426259+00:00
-- url     : https://prove2.me/theorems/34ffe942-4d8c-4357-9cc3-63d74d91e524
-- title:
--   Periodic Cubical4: toric Syndrome dual Membrane
-- statement:
--   The exact selected-generator syndrome of a partial dual membrane.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L84-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L84-L98

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.toricSyndrome_dualMembrane (m : PartialDualMembrane (L := L)) :
    stabilizerSyndrome (toricGenerator (L := L)) (dualMembraneError m) =
      Sum.elim (0 : Word (ZMod 2) (Link L)) (dualDefectLoop m) := by sorry
