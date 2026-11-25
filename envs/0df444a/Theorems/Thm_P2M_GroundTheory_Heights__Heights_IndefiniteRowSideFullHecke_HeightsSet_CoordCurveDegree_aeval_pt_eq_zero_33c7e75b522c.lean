-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_aeval_pt_eq_zero_33c7e75b522c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_aeval_pt_eq_zero_33c7e75b522c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:48:50.23959+00:00
-- url     : https://prove2.me/theorems/7ed60f92-2ddd-5096-9462-a70f487c4007
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree aeval pt eq zero 33c7e75b522c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heig
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree aeval pt eq zero 33c7e75b522c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree aeval pt eq zero 33c7e75b522c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCoordCurveDegree.lean#L121-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCoordCurveDegree.lean#L121-L162

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_aeval_pt_eq_zero_33c7e75b522c {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (d : ∀ k, ι k)
    (hyd : ∀ k, y ⟨k, d k⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : ∀ k, z ⟨k, d k⟩ ≠ 0) {g : MvPolynomial (Σ k, ι k) ℚ}
    (hg0 : aeval (fun p ↦ y p / y ⟨p.1, d p.1⟩) g = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, d p.1⟩) g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«CoordCurveDegree».«aeval_pt_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_aeval_pt_eq_zero_33c7e75b522c
