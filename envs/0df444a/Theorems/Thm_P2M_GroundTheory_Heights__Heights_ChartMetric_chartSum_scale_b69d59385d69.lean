-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_scale_b69d59385d69
-- name    : P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_scale_b69d59385d69
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:06.028175+00:00
-- url     : https://prove2.me/theorems/e908ab9e-a39b-567b-afa2-b8f5ba364e6a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Metric chart Sum scale b69d59385d69: P2 M Ground Theory Heights  Heights Chart Metric chart Sum scale b69d59385d69
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Metric chart Sum scale b69d59385d69 construction uses the P2 M Ground Theory Heights  Heights Chart Metric chart Sum scale b69d59385d69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L46-L51

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

theorem P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_scale_b69d59385d69 {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (t : ι → ℂ) (z : Cone n ℂ) (d : ι → ℕ) :
    ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (fun k i ↦ t k * z k i) (chartMonomial c d)‖ ^ 2 =
      (∏ k, ‖t k‖ ^ (2 * (d k : ℤ))) * ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone z (chartMonomial c d)‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMetric».«chartSum_scale» := P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_scale_b69d59385d69
