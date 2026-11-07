-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_HammingWeight_transpose_boundary3_cellWord_le_four
-- name    : QEC.Coding.PeriodicCubical4.HammingWeight_transpose_boundary3_cellWord_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:36:28.997892+00:00
-- url     : https://prove2.me/theorems/5a0cbbd3-e959-4162-90ae-70a7bd9a3e63
-- title:
--   Periodic Cubical4: Hamming Weight transpose boundary3 cell Word le four
-- statement:
--   A single dual plaquette has at most four incident-cube defects.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L252-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L252-L255

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.HammingWeight_transpose_boundary3_cellWord_le_four (p : Plaquette L) :
    HammingWeight (wordLinearMapTranspose boundary3 (cellWord p)) ≤ 4 := by sorry
