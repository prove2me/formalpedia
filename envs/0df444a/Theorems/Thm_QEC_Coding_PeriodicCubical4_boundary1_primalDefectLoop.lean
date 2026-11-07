-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary1_primalDefectLoop
-- name    : QEC.Coding.PeriodicCubical4.boundary1_primalDefectLoop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:48:30.465198+00:00
-- url     : https://prove2.me/theorems/90e5bee6-b962-4681-8d9a-d2bcf44f6900
-- title:
--   Periodic Cubical4: boundary1 primal Defect Loop
-- statement:
--   A primal membrane syndrome is a closed link loop.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L101-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L101-L105

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.boundary1_primalDefectLoop (m : PartialPrimalMembrane (L := L)) :
    boundary1 (primalDefectLoop m) = 0 := by sorry
