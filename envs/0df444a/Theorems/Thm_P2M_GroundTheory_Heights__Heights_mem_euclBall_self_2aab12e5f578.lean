-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_euclBall_self_2aab12e5f578
-- name    : P2M_GroundTheory_Heights__Heights_mem_euclBall_self_2aab12e5f578
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:32.267432+00:00
-- url     : https://prove2.me/theorems/e4b1958d-991e-46e8-b547-1c730b6d0eb5
-- title:
--   P2 M Ground Theory Heights  Heights mem eucl Ball self 2aab12e5f578: P2 M Ground Theory Heights  Heights mem eucl Ball self 2aab12e5f578
-- statement:
--   The P2 M Ground Theory Heights  Heights mem eucl Ball self 2aab12e5f578 construction uses the P2 M Ground Theory Heights  Heights mem eucl Ball self 2aab12e5f578 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegLelongMono.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegLelongMono.lean#L20-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_mem_euclBall_self_2aab12e5f578 {n : ℕ} (x : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) : x ∈ euclBall x ρ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_euclBall_self» := P2M_GroundTheory_Heights__Heights_mem_euclBall_self_2aab12e5f578
