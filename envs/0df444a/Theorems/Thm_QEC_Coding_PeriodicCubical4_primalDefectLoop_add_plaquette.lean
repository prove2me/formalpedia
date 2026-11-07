-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalDefectLoop_add_plaquette
-- name    : QEC.Coding.PeriodicCubical4.primalDefectLoop_add_plaquette
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:38:42.833506+00:00
-- url     : https://prove2.me/theorems/1bc71d52-ccff-4326-b295-e34cbc9e83ed
-- title:
--   Periodic Cubical4: primal Defect Loop add plaquette
-- statement:
--   Toggling one primal plaquette toggles exactly its four boundary links.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L258-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L258-L262

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalDefectLoop_add_plaquette
    (m : PartialPrimalMembrane (L := L)) (p : Plaquette L) :
    primalDefectLoop (m + cellWord p) =
      primalDefectLoop m + plaquetteBoundary p := by sorry
