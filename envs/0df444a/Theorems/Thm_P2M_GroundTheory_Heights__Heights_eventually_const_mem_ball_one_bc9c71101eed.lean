-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eventually_const_mem_ball_one_bc9c71101eed
-- name    : P2M_GroundTheory_Heights__Heights_eventually_const_mem_ball_one_bc9c71101eed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:35:20.501741+00:00
-- url     : https://prove2.me/theorems/0496a6bd-c30f-42c4-ad1a-0a5a75f54382
-- title:
--   P2 M Ground Theory Heights  Heights eventually const mem ball one bc9c71101eed: P2 M Ground Theory Heights  Heights eventually const mem ball one bc9c71101eed
-- statement:
--   The P2 M Ground Theory Heights  Heights eventually const mem ball one bc9c71101eed construction uses the P2 M Ground Theory Heights  Heights eventually const mem ball one bc9c71101eed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrdersLiftCentre.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrdersLiftCentre.lean#L9-L12

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

theorem P2M_GroundTheory_Heights__Heights_eventually_const_mem_ball_one_bc9c71101eed {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (0 : ℂ), (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eventually_const_mem_ball_one» := P2M_GroundTheory_Heights__Heights_eventually_const_mem_ball_one_bc9c71101eed
