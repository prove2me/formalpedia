-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_of_rhsR_7004e75546e9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_of_rhsR_7004e75546e9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:57.845814+00:00
-- url     : https://prove2.me/theorems/a6eb5066-edec-571f-9a1a-0d4a9be5e896
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family equiv of rhs R 7004e75546e9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family equiv
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family equiv of rhs R 7004e75546e9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family equiv of rhs R 7004e75546e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L38-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L38-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_of_rhsR_7004e75546e9 (I : Family ι)
    (hR : ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι),
      rhsR I P L A s = recR I P L A s) :
    IsFamily I ↔ IsIntersectionFamily I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«IsFamily».«equiv_of_rhsR» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_of_rhsR_7004e75546e9
