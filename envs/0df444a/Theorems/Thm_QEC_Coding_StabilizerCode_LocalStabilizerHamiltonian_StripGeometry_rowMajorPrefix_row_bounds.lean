-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_rowMajorPrefix_row_bounds
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.rowMajorPrefix_row_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:15:27.626199+00:00
-- url     : https://prove2.me/theorems/6fde14e8-6785-4da9-addb-7548aadf7176
-- title:
--   Strip Geometry: row Major Prefix row bounds
-- statement:
--   The Strip Geometry construction uses the row Major Prefix row bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L369-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L369-L389

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.rowMajorPrefix_row_bounds
    {L n : Nat} (hL : 0 < L) (p q : Site L)
    (hp : p ∈ rowMajorPrefix L n)
    (hq : q ∉ rowMajorPrefix L n) :
    p.2.val ≤ n / L ∧ n / L ≤ q.2.val := by sorry
