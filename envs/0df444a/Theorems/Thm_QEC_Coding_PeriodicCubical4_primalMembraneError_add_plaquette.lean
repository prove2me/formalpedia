-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalMembraneError_add_plaquette
-- name    : QEC.Coding.PeriodicCubical4.primalMembraneError_add_plaquette
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:49:37.805603+00:00
-- url     : https://prove2.me/theorems/ee6ebb7e-3c1c-4754-9398-7bd46e13959b
-- title:
--   Periodic Cubical4: primal Membrane Error add plaquette
-- statement:
--   The partial-membrane Pauli itself is updated by one pure-Z plaquette.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L272-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L272-L276

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalMembraneError_add_plaquette
    (m : PartialPrimalMembrane (L := L)) (p : Plaquette L) :
    binaryMul (primalMembraneError m) (primalMembraneError (cellWord p)) =
      primalMembraneError (m + cellWord p) := by sorry
