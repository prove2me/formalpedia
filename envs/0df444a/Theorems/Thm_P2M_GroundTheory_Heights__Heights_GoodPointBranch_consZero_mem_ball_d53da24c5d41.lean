-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_mem_ball_d53da24c5d41
-- name    : P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_mem_ball_d53da24c5d41
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:10.821886+00:00
-- url     : https://prove2.me/theorems/81c09c20-2902-4eb1-a74f-45bb1911a35b
-- title:
--   P2 M Ground Theory Heights  Heights Good Point Branch cons Zero mem ball d53da24c5d41: P2 M Ground Theory Heights  Heights Good Point Branch cons Zero mem ball d53da24c5d41
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Point Branch cons Zero mem ball d53da24c5d41 construction uses the P2 M Ground Theory Heights  Heights Good Point Branch cons Zero mem ball d53da24c5d41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L35-L44

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

theorem P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_mem_ball_d53da24c5d41 {d : ℕ} {s : ℝ} {v : Fin d → ℂ} (hv : v ∈ ball (0 : Fin d → ℂ) s) :
    consZero d v ∈ ball (0 : Fin (d + 1) → ℂ) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodPointBranch».«consZero_mem_ball» := P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_mem_ball_d53da24c5d41
