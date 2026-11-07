-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openVerticalInterval_iff
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openVerticalInterval_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:31:31.811369+00:00
-- url     : https://prove2.me/theorems/58e3e6e9-0c7d-43d0-8097-0ab3441052f4
-- title:
--   Strip Geometry: mem open Vertical Interval iff
-- statement:
--   The Strip Geometry construction uses the mem open Vertical Interval iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L133-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L133-L137

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openVerticalInterval_iff
    {L start width : Nat} (p : Site L) :
    p ∈ openVerticalInterval L start width ↔
      start ≤ p.1.val ∧ p.1.val < start + width := by sorry
