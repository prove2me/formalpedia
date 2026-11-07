-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_movingFrontier_iff
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_movingFrontier_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:16:08.896124+00:00
-- url     : https://prove2.me/theorems/9f3dac3e-951b-4864-a413-7aaaf1e4924e
-- title:
--   Strip Geometry: mem moving Frontier iff
-- statement:
--   The Strip Geometry construction uses the mem moving Frontier iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L472-L477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L472-L477

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_movingFrontier_iff
    {L stripStart stripWidth cursor r : Nat} (p : Site L) :
    p ∈ movingFrontier L stripStart stripWidth cursor r ↔
      p ∈ openVerticalInterval L stripStart stripWidth ∧
        p.2.val ≤ cursor ∧ cursor < p.2.val + r := by sorry
