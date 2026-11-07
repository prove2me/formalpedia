-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_rowMajorExactPath_endpoint
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.rowMajorExactPath_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:15:10.928231+00:00
-- url     : https://prove2.me/theorems/054e3369-e4a0-4ec5-a74e-c9e65f4f9600
-- title:
--   Strip Geometry: row Major Exact Path endpoint
-- statement:
--   The Strip Geometry construction uses the row Major Exact Path endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L398-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L398-L402

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.rowMajorExactPath_endpoint
    {L : Nat} (Q : Binary (Site L)) :
    (rowMajorExactPath Q).endpoint = Q := by sorry
