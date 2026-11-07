-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_transpose_boundary4_dualDefectLoop
-- name    : QEC.Coding.PeriodicCubical4.transpose_boundary4_dualDefectLoop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:49:25.43387+00:00
-- url     : https://prove2.me/theorems/a05e8f7e-ed4c-4e81-92b5-686c3492aa8f
-- title:
--   Periodic Cubical4: transpose boundary4 dual Defect Loop
-- statement:
--   A dual membrane syndrome is a closed dual-link loop (a cube 1-chain).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L108-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L108-L119

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.transpose_boundary4_dualDefectLoop (m : PartialDualMembrane (L := L)) :
    wordLinearMapTranspose boundary4 (dualDefectLoop m) = 0 := by sorry
