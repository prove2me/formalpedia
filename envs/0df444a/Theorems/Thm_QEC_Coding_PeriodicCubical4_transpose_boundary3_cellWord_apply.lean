-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_transpose_boundary3_cellWord_apply
-- name    : QEC.Coding.PeriodicCubical4.transpose_boundary3_cellWord_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:36:23.566554+00:00
-- url     : https://prove2.me/theorems/9303318b-0614-4473-ad31-078f39346ef2
-- title:
--   Periodic Cubical4: transpose boundary3 cell Word apply
-- statement:
--   Transposing the cube boundary evaluates a plaquette against that boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L213-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L213-L229

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.transpose_boundary3_cellWord_apply (p : Plaquette L) (c : Cube L) :
    wordLinearMapTranspose boundary3 (cellWord p) c = cubeBoundary c p := by sorry
