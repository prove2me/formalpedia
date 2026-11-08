-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualMembraneError_add_plaquette
-- name    : QEC.Coding.PeriodicCubical4.dualMembraneError_add_plaquette
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:49:40.324764+00:00
-- url     : https://prove2.me/theorems/eae1af2f-19dd-4ffd-8167-58636880a5f7
-- title:
--   Periodic Cubical4: dual Membrane Error add plaquette
-- statement:
--   The partial-membrane Pauli itself is updated by one pure-X plaquette.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L279-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L279-L283

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualMembraneError_add_plaquette
    (m : PartialDualMembrane (L := L)) (p : Plaquette L) :
    binaryMul (dualMembraneError m) (dualMembraneError (cellWord p)) =
      dualMembraneError (m + cellWord p) := by sorry
