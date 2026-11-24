-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_ball_pi_complex_2b227a46408d
-- name    : P2M_GroundTheory_Heights__Heights_volume_ball_pi_complex_2b227a46408d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:56.280625+00:00
-- url     : https://prove2.me/theorems/374ce855-e6c0-4f42-a553-eb2fb617347e
-- title:
--   P2 M Ground Theory Heights  Heights volume ball pi complex 2b227a46408d: P2 M Ground Theory Heights  Heights volume ball pi complex 2b227a46408d
-- statement:
--   The P2 M Ground Theory Heights  Heights volume ball pi complex 2b227a46408d construction uses the P2 M Ground Theory Heights  Heights volume ball pi complex 2b227a46408d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetBallCover.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetBallCover.lean#L12-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
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
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_volume_ball_pi_complex_2b227a46408d {n : ℕ} (c : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball c ρ) = ENNReal.ofReal ((Real.pi * ρ ^ 2) ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«volume_ball_pi_complex» := P2M_GroundTheory_Heights__Heights_volume_ball_pi_complex_2b227a46408d
