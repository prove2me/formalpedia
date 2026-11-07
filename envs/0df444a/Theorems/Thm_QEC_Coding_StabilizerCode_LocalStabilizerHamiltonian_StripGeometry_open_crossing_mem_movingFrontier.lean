-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_open_crossing_mem_movingFrontier
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.open_crossing_mem_movingFrontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:17:03.447075+00:00
-- url     : https://prove2.me/theorems/1cdaddb6-5248-4275-bc21-1f363c2ca49a
-- title:
--   Strip Geometry: open crossing mem moving Frontier
-- statement:
--   The Strip Geometry construction uses the open crossing mem moving Frontier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L580-L597
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L580-L597

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.open_crossing_mem_movingFrontier
    {L r stripStart stripWidth cursor : Nat}
    {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (hLocal : HasOpenRowIntervalGeneratorSupport H r)
    (j : κ) (p q : Site L)
    (hpGenerator : p ∈ support (H.generators j))
    (hqGenerator : q ∈ support (H.generators j))
    (hpStrip : p ∈ openVerticalInterval L stripStart stripWidth)
    (hpCursor : p.2.val ≤ cursor) (hCursorQ : cursor ≤ q.2.val) :
    p ∈ movingFrontier L stripStart stripWidth cursor r := by sorry
