-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_ab88e3b42d04
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_ab88e3b42d04
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:52.656033+00:00
-- url     : https://prove2.me/theorems/243cda59-fb27-459a-91e3-daf6d9c836b9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family equiv ab88e3b42d04: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family equiv ab88e3b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family equiv ab88e3b42d04 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family equiv ab88e3b42d04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermTensor.lean#L77-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rhsR_equiv_ab54d4a8ce7e

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_ab88e3b42d04 (I : Family ι) : IsFamily I ↔ IsIntersectionFamily I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«IsFamily».«equiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_ab88e3b42d04
