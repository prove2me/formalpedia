-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_take_rowMajorSites_iff
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_take_rowMajorSites_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:16:37.172398+00:00
-- url     : https://prove2.me/theorems/5e56b016-1945-4694-99eb-801d3dc5b75d
-- title:
--   Strip Geometry: mem take row Major Sites iff
-- statement:
--   The Strip Geometry construction uses the mem take row Major Sites iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L301-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L301-L316

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_take_rowMajorSites_iff
    {L n : Nat} (p : Site L) :
    p ∈ (rowMajorSites L).take n ↔
      rowMajorIndex p < min n (L * L) := by sorry
