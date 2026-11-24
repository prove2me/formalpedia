-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_analyticAt_eval_disc_feccb63fcfb3
-- name    : P2M_GroundTheory_Heights__Heights_analyticAt_eval_disc_feccb63fcfb3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:56.751055+00:00
-- url     : https://prove2.me/theorems/dae57aca-abe6-46b9-8f44-e873a65e68ba
-- title:
--   P2 M Ground Theory Heights  Heights analytic At eval disc feccb63fcfb3: P2 M Ground Theory Heights  Heights analytic At eval disc feccb63fcfb3
-- statement:
--   The P2 M Ground Theory Heights  Heights analytic At eval disc feccb63fcfb3 construction uses the P2 M Ground Theory Heights  Heights analytic At eval disc feccb63fcfb3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L87-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L87-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder
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
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}

theorem P2M_GroundTheory_Heights__Heights_analyticAt_eval_disc_feccb63fcfb3 [Fintype σ] {r : ℝ} (hr : 0 < r) {φ : (Fin 1 → ℂ) → σ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) (g : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«analyticAt_eval_disc» := P2M_GroundTheory_Heights__Heights_analyticAt_eval_disc_feccb63fcfb3
