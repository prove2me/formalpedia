-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_algebraAdjoin_eq_finrank_adjoin_78e55535a125
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_algebraAdjoin_eq_finrank_adjoin_78e55535a125
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:41:34.30525+00:00
-- url     : https://prove2.me/theorems/eb853563-d3c9-478e-8145-af9a0fcaffb4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac finrank algebra Adjoin eq finrank adjoin 78e55535a125: P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac finrank algebra Adjoin eq f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac finrank algebra Adjoin eq finrank adjoin 78e55535a125 construction uses the P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac finrank algebra Adjoin eq finrank adjoin 78e55535a125 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRankAdjoinFrac.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRankAdjoinFrac.lean#L13-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRankAdjoinFrac
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Module IntermediateField IntermediateField.algebraAdjoinAdjoin
open GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac

theorem P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_algebraAdjoin_eq_finrank_adjoin_78e55535a125 {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (T : Set Ω) :
    finrank K (Algebra.adjoin K T) = finrank K (IntermediateField.adjoin K T) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RankAdjoinFrac».«finrank_algebraAdjoin_eq_finrank_adjoin» := P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_algebraAdjoin_eq_finrank_adjoin_78e55535a125
