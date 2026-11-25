-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_tail_mem_ball_2a892ce3fe7b
-- name    : P2M_GroundTheory_Heights__Heights_GoodPointBranch_tail_mem_ball_2a892ce3fe7b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:18.857571+00:00
-- url     : https://prove2.me/theorems/f4f0c569-6f34-4380-8e27-b6e78c0584ab
-- title:
--   P2 M Ground Theory Heights  Heights Good Point Branch tail mem ball 2a892ce3fe7b: P2 M Ground Theory Heights  Heights Good Point Branch tail mem ball 2a892ce3fe7b
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Point Branch tail mem ball 2a892ce3fe7b construction uses the P2 M Ground Theory Heights  Heights Good Point Branch tail mem ball 2a892ce3fe7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L46-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch

theorem P2M_GroundTheory_Heights__Heights_GoodPointBranch_tail_mem_ball_2a892ce3fe7b {d : ℕ} {s : ℝ} {t : Fin (d + 1) → ℂ} (ht : t ∈ ball (0 : Fin (d + 1) → ℂ) s) :
    Fin.tail t ∈ ball (0 : Fin d → ℂ) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodPointBranch».«tail_mem_ball» := P2M_GroundTheory_Heights__Heights_GoodPointBranch_tail_mem_ball_2a892ce3fe7b
