-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPreconnected_punctured_ball_7486948dcaa3
-- name    : P2M_GroundTheory_Heights__Heights_isPreconnected_punctured_ball_7486948dcaa3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:21.690585+00:00
-- url     : https://prove2.me/theorems/7e74c999-bfd3-4f10-b774-ec8107c1eb09
-- title:
--   P2 M Ground Theory Heights  Heights is Preconnected punctured ball 7486948dcaa3: P2 M Ground Theory Heights  Heights is Preconnected punctured ball 7486948dcaa3
-- statement:
--   The P2 M Ground Theory Heights  Heights is Preconnected punctured ball 7486948dcaa3 construction uses the P2 M Ground Theory Heights  Heights is Preconnected punctured ball 7486948dcaa3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchInOneBranch.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchInOneBranch.lean#L10-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchInOneBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchImageNhdOffCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchInOneBranch
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
open MvPolynomial ComplexSets Filter Topology

theorem P2M_GroundTheory_Heights__Heights_isPreconnected_punctured_ball_7486948dcaa3 {R : ℝ} (hR : 0 < R) :
    IsPreconnected (Metric.ball (0 : ℂ) R \ {0}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isPreconnected_punctured_ball» := P2M_GroundTheory_Heights__Heights_isPreconnected_punctured_ball_7486948dcaa3
