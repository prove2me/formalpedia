-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_euclBall_iff_5e33abc501c8
-- name    : P2M_GroundTheory_Heights__Heights_mem_euclBall_iff_5e33abc501c8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:53.998965+00:00
-- url     : https://prove2.me/theorems/3bbc9334-dcd6-5998-b3a5-54f756b1cce5
-- title:
--   P2 M Ground Theory Heights  Heights mem eucl Ball iff 5e33abc501c8: P2 M Ground Theory Heights  Heights mem eucl Ball iff 5e33abc501c8
-- statement:
--   The P2 M Ground Theory Heights  Heights mem eucl Ball iff 5e33abc501c8 construction uses the P2 M Ground Theory Heights  Heights mem eucl Ball iff 5e33abc501c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegLelongMono.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegLelongMono.lean#L15-L18

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

theorem P2M_GroundTheory_Heights__Heights_mem_euclBall_iff_5e33abc501c8 {n : ℕ} (x y : Fin n → ℂ) (ρ : ℝ) :
    y ∈ euclBall x ρ ↔ dist (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 x) < ρ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_euclBall_iff» := P2M_GroundTheory_Heights__Heights_mem_euclBall_iff_5e33abc501c8
