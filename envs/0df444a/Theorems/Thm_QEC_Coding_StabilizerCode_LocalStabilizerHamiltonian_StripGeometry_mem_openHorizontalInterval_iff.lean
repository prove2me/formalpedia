-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openHorizontalInterval_iff
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openHorizontalInterval_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:15:16.578192+00:00
-- url     : https://prove2.me/theorems/fee31779-146e-48b4-8719-816d3771e1d3
-- title:
--   Strip Geometry: mem open Horizontal Interval iff
-- statement:
--   The Strip Geometry construction uses the mem open Horizontal Interval iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L427-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L427-L431

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openHorizontalInterval_iff
    {L start width : Nat} (p : Site L) :
    p ∈ openHorizontalInterval L start width ↔
      start ≤ p.2.val ∧ p.2.val < start + width := by sorry
