-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualDefectLoop_add_plaquette
-- name    : QEC.Coding.PeriodicCubical4.dualDefectLoop_add_plaquette
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:38:19.182569+00:00
-- url     : https://prove2.me/theorems/ebdfefa2-566c-4f8c-9276-8f4f25d50cea
-- title:
--   Periodic Cubical4: dual Defect Loop add plaquette
-- statement:
--   Toggling one dual plaquette toggles exactly its incident dual links.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L265-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L265-L269

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualDefectLoop_add_plaquette
    (m : PartialDualMembrane (L := L)) (p : Plaquette L) :
    dualDefectLoop (m + cellWord p) =
      dualDefectLoop m + wordLinearMapTranspose boundary3 (cellWord p) := by sorry
