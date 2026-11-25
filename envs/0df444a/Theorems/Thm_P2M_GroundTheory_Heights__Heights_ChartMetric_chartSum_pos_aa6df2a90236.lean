-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_pos_aa6df2a90236
-- name    : P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_pos_aa6df2a90236
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:17.046612+00:00
-- url     : https://prove2.me/theorems/7c81401c-4768-4a09-8a1b-3034546ae7f7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Metric chart Sum pos aa6df2a90236: P2 M Ground Theory Heights  Heights Chart Metric chart Sum pos aa6df2a90236
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Metric chart Sum pos aa6df2a90236 construction uses the P2 M Ground Theory Heights  Heights Chart Metric chart Sum pos aa6df2a90236 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L53-L62

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

theorem P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_pos_aa6df2a90236 {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {z : Cone n ℂ}
    (hz : BlockNonzero z) (d : ι → ℕ) :
    0 < ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone z (chartMonomial c d)‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMetric».«chartSum_pos» := P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_pos_aa6df2a90236
