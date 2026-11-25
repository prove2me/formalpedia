-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_cc429de364eb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_cc429de364eb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:50.060879+00:00
-- url     : https://prove2.me/theorems/0df1645b-3e64-486b-9f50-5d7fe478ad7d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec iff cc429de364eb: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec iff cc429de364eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec iff cc429de364eb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec iff cc429de364eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L30-L36

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_cc429de364eb (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    IsSec P A s ↔ ∃ a : K → ℕ, (∀ k, A.a k = a k) ∧ IsMultiHomog s a ∧ s ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isSec_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_cc429de364eb
