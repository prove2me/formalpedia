-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_cols_6dbf82d8b420
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_cols_6dbf82d8b420
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:56.737448+00:00
-- url     : https://prove2.me/theorems/9397ddda-2da1-4a98-9d13-bb5fd99f1909
-- title:
--   P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of cols 6dbf82d8b420: P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of cols 6dbf82d8b420
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of cols 6dbf82d8b420 construction uses the P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of cols 6dbf82d8b420 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L33-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L33-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
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
open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_cols_6dbf82d8b420 (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (S C : Finset (Fin D))
    (hcard : D < C.card + S.card) (hB : ∀ k ∈ S, ∀ j ∈ C, ∀ i, B k i j = 0) : mixedDisc B = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mixedDisc_eq_zero_of_cols» := P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_cols_6dbf82d8b420
