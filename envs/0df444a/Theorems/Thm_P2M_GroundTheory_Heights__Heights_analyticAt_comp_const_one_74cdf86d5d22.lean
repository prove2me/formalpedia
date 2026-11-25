-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_analyticAt_comp_const_one_74cdf86d5d22
-- name    : P2M_GroundTheory_Heights__Heights_analyticAt_comp_const_one_74cdf86d5d22
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:01.750081+00:00
-- url     : https://prove2.me/theorems/5f50232e-5032-4d35-8f4e-6ea56d274530
-- title:
--   P2 M Ground Theory Heights  Heights analytic At comp const one 74cdf86d5d22: P2 M Ground Theory Heights  Heights analytic At comp const one 74cdf86d5d22
-- statement:
--   The P2 M Ground Theory Heights  Heights analytic At comp const one 74cdf86d5d22 construction uses the P2 M Ground Theory Heights  Heights analytic At comp const one 74cdf86d5d22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrdersLiftCentre.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrdersLiftCentre.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrdersLiftCentre
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
open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem P2M_GroundTheory_Heights__Heights_analyticAt_comp_const_one_74cdf86d5d22 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {φ : (Fin 1 → ℂ) → E} {r : ℝ} (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) :
    AnalyticAt ℂ (fun τ : ℂ ↦ φ (fun _ ↦ τ)) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«analyticAt_comp_const_one» := P2M_GroundTheory_Heights__Heights_analyticAt_comp_const_one_74cdf86d5d22
