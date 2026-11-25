-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_eq_finrank_algebraAdjoin_f7378cb62581
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_eq_finrank_algebraAdjoin_f7378cb62581
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:41:26.000983+00:00
-- url     : https://prove2.me/theorems/eeaec6e2-85bd-4aec-8926-a714667c1d58
-- title:
--   P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac finrank eq finrank algebra Adjoin f7378cb62581: P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac finrank eq finrank algebra Adjoin
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac finrank eq finrank algebra Adjoin f7378cb62581 construction uses the P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac finrank eq finrank algebra Adjoin f7378cb62581 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRankAdjoinFrac.lean#L65-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRankAdjoinFrac.lean#L65-L115

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_eq_finrank_algebraAdjoin_f7378cb62581 {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω}
    (h : S ⊆ T) :
    letI := adjoinInclAlgebra F h
    finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RankAdjoinFrac».«finrank_eq_finrank_algebraAdjoin» := P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_eq_finrank_algebraAdjoin_f7378cb62581
