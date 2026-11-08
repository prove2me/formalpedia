-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalLoopLength_add_plaquette_le
-- name    : QEC.Coding.PeriodicCubical4.primalLoopLength_add_plaquette_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:49:41.342955+00:00
-- url     : https://prove2.me/theorems/d91898f7-22fb-47a2-91dc-58de4907d555
-- title:
--   Periodic Cubical4: primal Loop Length add plaquette le
-- statement:
--   One primal plaquette step can increase loop length by at most four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L286-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L286-L292

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalLoopLength_add_plaquette_le
    (m : PartialPrimalMembrane (L := L)) (p : Plaquette L) :
    primalLoopLength (m + cellWord p) ≤ primalLoopLength m + 4 := by sorry
