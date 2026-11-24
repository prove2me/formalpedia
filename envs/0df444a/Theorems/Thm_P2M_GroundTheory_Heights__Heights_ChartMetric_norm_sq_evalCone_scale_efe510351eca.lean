-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_norm_sq_evalCone_scale_efe510351eca
-- name    : P2M_GroundTheory_Heights__Heights_ChartMetric_norm_sq_evalCone_scale_efe510351eca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:26.399583+00:00
-- url     : https://prove2.me/theorems/479d14e1-7d70-4508-b197-db13230d9946
-- title:
--   P2 M Ground Theory Heights  Heights Chart Metric norm sq eval Cone scale efe510351eca: P2 M Ground Theory Heights  Heights Chart Metric norm sq eval Cone scale efe510351eca
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Metric norm sq eval Cone scale efe510351eca construction uses the P2 M Ground Theory Heights  Heights Chart Metric norm sq eval Cone scale efe510351eca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L33-L44

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

theorem P2M_GroundTheory_Heights__Heights_ChartMetric_norm_sq_evalCone_scale_efe510351eca {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (t : ι → ℂ) (z : Cone n ℂ)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    ‖evalCone (fun k i ↦ t k * z k i) f‖ ^ 2 = (∏ k, ‖t k‖ ^ (2 * (δ k : ℤ))) * ‖evalCone z f‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMetric».«norm_sq_evalCone_scale» := P2M_GroundTheory_Heights__Heights_ChartMetric_norm_sq_evalCone_scale_efe510351eca
