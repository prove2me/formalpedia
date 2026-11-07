-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_hammingSupport_transpose_boundary3_cellWord
-- name    : QEC.Coding.PeriodicCubical4.hammingSupport_transpose_boundary3_cellWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:36:13.723849+00:00
-- url     : https://prove2.me/theorems/7e1d3cf5-53c4-4822-9c71-4faa31c09df4
-- title:
--   Periodic Cubical4: hamming Support transpose boundary3 cell Word
-- statement:
--   The support of one dual plaquette coboundary is its incident-cube set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L232-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L232-L243

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.hammingSupport_transpose_boundary3_cellWord (p : Plaquette L) :
    hammingSupport (wordLinearMapTranspose boundary3 (cellWord p)) =
      plaquetteCubes p := by sorry
