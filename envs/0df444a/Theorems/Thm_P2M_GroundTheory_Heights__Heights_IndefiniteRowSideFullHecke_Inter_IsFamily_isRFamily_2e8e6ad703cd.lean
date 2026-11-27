-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_isRFamily_2e8e6ad703cd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_isRFamily_2e8e6ad703cd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:15.922826+00:00
-- url     : https://prove2.me/theorems/ca1f3392-2105-5973-ad06-b58a86e04fa2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family is RFamily 2e8e6ad703cd: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family is RFamil
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family is RFamily 2e8e6ad703cd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Is Family is RFamily 2e8e6ad703cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UniquenessDegreeFormOfIntersectionForm.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UniquenessDegreeFormOfIntersectionForm.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I2_IsIntersectionFamily_isRFamily

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_isRFamily_2e8e6ad703cd {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {I : Family ι}
    (h : IsFamily I) : IsRFamily I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«IsFamily».«isRFamily» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_isRFamily_2e8e6ad703cd
