-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_update_6724d9a7040a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_update_6724d9a7040a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:00:57.721402+00:00
-- url     : https://prove2.me/theorems/be3501d8-7495-52fa-8cda-f7656d088fa6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter all Smooth update 6724d9a7040a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter all Smooth update 6724
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter all Smooth update 6724d9a7040a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter all Smooth update 6724d9a7040a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L16-L21

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_update_6724d9a7040a {n : ℕ} {L : Fin n → HermLine ι} (hL : AllSmooth L) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : AllSmooth (Function.update L j X) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«allSmooth_update» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_update_6724d9a7040a
