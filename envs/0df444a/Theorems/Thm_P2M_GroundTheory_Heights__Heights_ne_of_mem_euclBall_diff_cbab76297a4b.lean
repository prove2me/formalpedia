-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ne_of_mem_euclBall_diff_cbab76297a4b
-- name    : P2M_GroundTheory_Heights__Heights_ne_of_mem_euclBall_diff_cbab76297a4b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:32.150175+00:00
-- url     : https://prove2.me/theorems/bcbc1e2e-d25b-4b1f-ad36-ae12b579fbea
-- title:
--   P2 M Ground Theory Heights  Heights ne of mem eucl Ball diff cbab76297a4b: P2 M Ground Theory Heights  Heights ne of mem eucl Ball diff cbab76297a4b
-- statement:
--   The P2 M Ground Theory Heights  Heights ne of mem eucl Ball diff cbab76297a4b construction uses the P2 M Ground Theory Heights  Heights ne of mem eucl Ball diff cbab76297a4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegLelongAnnulus.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegLelongAnnulus.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLogDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
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

theorem P2M_GroundTheory_Heights__Heights_ne_of_mem_euclBall_diff_cbab76297a4b {n : ℕ} {x z : Fin n → ℂ} {r s : ℝ} (hr : 0 < r)
    (hz : z ∈ euclBall x s \ euclBall x r) : z ≠ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ne_of_mem_euclBall_diff» := P2M_GroundTheory_Heights__Heights_ne_of_mem_euclBall_diff_cbab76297a4b
