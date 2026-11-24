-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_X_inr_7730eace2592
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_X_inr_7730eace2592
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:07.132939+00:00
-- url     : https://prove2.me/theorems/6c349bef-4d4a-43e6-bd6c-d77a935a5373
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Bundle Map X inr 7730eace2592: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Bundle Map X
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Bundle Map X inr 7730eace2592 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Bundle Map X inr 7730eace2592 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L91-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_X_inr_7730eace2592 (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (u : Unit) (j : Fin N1) :
    projBundleMap P B (X ⟨Sum.inr u, j⟩) = ∑ a, C (B a j) * X a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«projBundleMap_X_inr» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_X_inr_7730eace2592
