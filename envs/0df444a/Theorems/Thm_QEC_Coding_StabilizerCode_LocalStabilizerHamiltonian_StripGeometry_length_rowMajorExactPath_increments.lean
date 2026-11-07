-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_length_rowMajorExactPath_increments
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.length_rowMajorExactPath_increments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:14:51.158954+00:00
-- url     : https://prove2.me/theorems/9293272f-34f5-418e-9127-3a8136eeb7cc
-- title:
--   Strip Geometry: length row Major Exact Path increments
-- statement:
--   The Strip Geometry construction uses the length row Major Exact Path increments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L415-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L415-L419

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.length_rowMajorExactPath_increments
    {L : Nat} (Q : Binary (Site L)) :
    (rowMajorExactPath Q).increments.length = L * L + 1 := by sorry
