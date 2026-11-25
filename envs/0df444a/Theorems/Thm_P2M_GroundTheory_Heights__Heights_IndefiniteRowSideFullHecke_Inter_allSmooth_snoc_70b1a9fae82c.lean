-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_snoc_70b1a9fae82c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_snoc_70b1a9fae82c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:16.75188+00:00
-- url     : https://prove2.me/theorems/82cb4b4f-b39e-457c-ab4a-3ee3df13fd74
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter all Smooth snoc 70b1a9fae82c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter all Smooth snoc 70b1a9fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter all Smooth snoc 70b1a9fae82c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter all Smooth snoc 70b1a9fae82c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L23-L28

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_snoc_70b1a9fae82c {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A : HermLine ι} (hA : IsSmoothHerm A) : AllSmooth (Fin.snoc L A : Fin (n + 1) → HermLine ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«allSmooth_snoc» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_snoc_70b1a9fae82c
