-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_integrableOn_inv_log_sq_mul_30145d823e46
-- name    : P2M_GroundTheory_Heights__Heights_integrableOn_inv_log_sq_mul_30145d823e46
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:59.949988+00:00
-- url     : https://prove2.me/theorems/90c0bc34-33bd-4056-9824-b6cbbdb27b43
-- title:
--   P2 M Ground Theory Heights  Heights integrable On inv log sq mul 30145d823e46: P2 M Ground Theory Heights  Heights integrable On inv log sq mul 30145d823e46
-- statement:
--   The P2 M Ground Theory Heights  Heights integrable On inv log sq mul 30145d823e46 construction uses the P2 M Ground Theory Heights  Heights integrable On inv log sq mul 30145d823e46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepWeightMass.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepWeightMass.lean#L16-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepWeightMass
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
open MeasureTheory Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_integrableOn_inv_log_sq_mul_30145d823e46 :
    IntegrableOn (fun r : ℝ => ((Real.log r) ^ 2 * r)⁻¹) (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«integrableOn_inv_log_sq_mul» := P2M_GroundTheory_Heights__Heights_integrableOn_inv_log_sq_mul_30145d823e46
