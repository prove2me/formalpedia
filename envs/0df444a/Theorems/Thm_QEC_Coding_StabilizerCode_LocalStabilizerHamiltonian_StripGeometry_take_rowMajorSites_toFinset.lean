-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_take_rowMajorSites_toFinset
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.take_rowMajorSites_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:16:52.872864+00:00
-- url     : https://prove2.me/theorems/8f887902-5d10-48f0-ba18-21294ed8b65f
-- title:
--   Strip Geometry: take row Major Sites to Finset
-- statement:
--   The Strip Geometry construction uses the take row Major Sites to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L342-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L342-L347

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.take_rowMajorSites_toFinset
    {L n : Nat} (hn : n ≤ L * L) :
    ((rowMajorSites L).take n).toFinset = rowMajorPrefix L n := by sorry
