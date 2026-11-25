-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_exists_ptOf_2ca38ad1a588
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_exists_ptOf_2ca38ad1a588
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:30:52.330304+00:00
-- url     : https://prove2.me/theorems/f60c67e7-04d1-5cdc-b20d-e09efc37c006
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree exists pt Of 2ca38ad1a588: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree exists pt Of 2ca38ad1a588 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree exists pt Of 2ca38ad1a588 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCoordCurveDegree.lean#L164-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCoordCurveDegree.lean#L164-L208

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_exists_ptOf_2ca38ad1a588 {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ φ : blockFnField y →ₐ[ℚ] ℂ, ptOf y c φ = (fun p ↦ (z ⟨p.1, c p.1⟩)⁻¹ * z p) ∧
      ∀ k, z ⟨k, c k⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«CoordCurveDegree».«exists_ptOf» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_exists_ptOf_2ca38ad1a588
