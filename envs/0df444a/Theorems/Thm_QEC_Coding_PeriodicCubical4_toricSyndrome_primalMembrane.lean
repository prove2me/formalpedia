-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_toricSyndrome_primalMembrane
-- name    : QEC.Coding.PeriodicCubical4.toricSyndrome_primalMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:35:51.136506+00:00
-- url     : https://prove2.me/theorems/9c0c291e-a72b-450c-a595-8a9f46db2bc1
-- title:
--   Periodic Cubical4: toric Syndrome primal Membrane
-- statement:
--   The exact selected-generator syndrome of a partial primal membrane.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L66-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L66-L81

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.toricSyndrome_primalMembrane (m : PartialPrimalMembrane (L := L)) :
    stabilizerSyndrome (toricGenerator (L := L)) (primalMembraneError m) =
      Sum.elim (primalDefectLoop m) (0 : Word (ZMod 2) (Cube L)) := by sorry
