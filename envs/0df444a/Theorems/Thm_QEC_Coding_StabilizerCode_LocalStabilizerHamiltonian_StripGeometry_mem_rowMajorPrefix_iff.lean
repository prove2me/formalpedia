-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_rowMajorPrefix_iff
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_rowMajorPrefix_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:14:38.325189+00:00
-- url     : https://prove2.me/theorems/cc754f6a-5ef5-4a61-8402-b4d5b66f095a
-- title:
--   Strip Geometry: mem row Major Prefix iff
-- statement:
--   The Strip Geometry construction uses the mem row Major Prefix iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L337-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L337-L340

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_rowMajorPrefix_iff
    {L n : Nat} (p : Site L) :
    p ∈ rowMajorPrefix L n ↔ rowMajorIndex p < n := by sorry
