-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_scale_alg_9e8d282e6431
-- name    : P2M_GroundTheory_Heights__Heights_ChartMetric_scale_alg_9e8d282e6431
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:21.293965+00:00
-- url     : https://prove2.me/theorems/d0a522ba-b246-5e3c-9f6c-6e60cada5ca7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Metric scale alg 9e8d282e6431: P2 M Ground Theory Heights  Heights Chart Metric scale alg 9e8d282e6431
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Metric scale alg 9e8d282e6431 construction uses the P2 M Ground Theory Heights  Heights Chart Metric scale alg 9e8d282e6431 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L97-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale
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
open MvPolynomial
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric

theorem P2M_GroundTheory_Heights__Heights_ChartMetric_scale_alg_9e8d282e6431 (A B h s L S Den : ℝ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < Den) :
    A * h * (s * L) * Real.sqrt (B * S / (B * A ^ 2 * Den)) = s * (h * L * Real.sqrt (S / Den)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMetric».«scale_alg» := P2M_GroundTheory_Heights__Heights_ChartMetric_scale_alg_9e8d282e6431
