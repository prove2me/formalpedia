-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyLelongMono_euclBall_measure_a192beebcffd
-- name    : P2M_GroundTheory_Heights__Heights_VarietyLelongMono_euclBall_measure_a192beebcffd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:41:45.708109+00:00
-- url     : https://prove2.me/theorems/2138d237-0800-483a-8fca-67b877843340
-- title:
--   P2 M Ground Theory Heights  Heights Variety Lelong Mono eucl Ball measure a192beebcffd: P2 M Ground Theory Heights  Heights Variety Lelong Mono eucl Ball measure a192beebcffd
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Lelong Mono eucl Ball measure a192beebcffd construction uses the P2 M Ground Theory Heights  Heights Variety Lelong Mono eucl Ball measure a192beebcffd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarietyLelongMono.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarietyLelongMono.lean#L19-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
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
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_VarietyLelongMono_euclBall_measure_a192beebcffd (d : ℕ) (z : EuclideanSpace ℂ (Fin d)) {r : ℝ} (hr : 0 < r) :
    μH[((2 * d : ℕ) : ℝ)] (Metric.ball z r) =
      ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietyLelongMono».«euclBall_measure» := P2M_GroundTheory_Heights__Heights_VarietyLelongMono_euclBall_measure_a192beebcffd
