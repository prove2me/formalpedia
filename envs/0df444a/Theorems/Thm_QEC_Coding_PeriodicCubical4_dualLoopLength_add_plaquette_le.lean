-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualLoopLength_add_plaquette_le
-- name    : QEC.Coding.PeriodicCubical4.dualLoopLength_add_plaquette_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:49:36.975507+00:00
-- url     : https://prove2.me/theorems/64cc1b10-2895-44d8-84aa-ebf097703aa3
-- title:
--   Periodic Cubical4: dual Loop Length add plaquette le
-- statement:
--   One dual plaquette step can increase loop length by at most four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L295-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L295-L303

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualLoopLength_add_plaquette_le
    (m : PartialDualMembrane (L := L)) (p : Plaquette L) :
    dualLoopLength (m + cellWord p) ≤ dualLoopLength m + 4 := by sorry
