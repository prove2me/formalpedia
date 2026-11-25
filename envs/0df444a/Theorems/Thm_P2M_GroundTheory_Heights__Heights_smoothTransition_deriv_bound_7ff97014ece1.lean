-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothTransition_deriv_bound_7ff97014ece1
-- name    : P2M_GroundTheory_Heights__Heights_smoothTransition_deriv_bound_7ff97014ece1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:17.245358+00:00
-- url     : https://prove2.me/theorems/611daa61-1292-46d6-aebf-37122e922f26
-- title:
--   P2 M Ground Theory Heights  Heights smooth Transition deriv bound 7ff97014ece1: P2 M Ground Theory Heights  Heights smooth Transition deriv bound 7ff97014ece1
-- statement:
--   The P2 M Ground Theory Heights  Heights smooth Transition deriv bound 7ff97014ece1 construction uses the P2 M Ground Theory Heights  Heights smooth Transition deriv bound 7ff97014ece1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessDeriv.lean#L23-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessDeriv.lean#L23-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessDeriv
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
open Filter Topology
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_smoothTransition_deriv_bound_7ff97014ece1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C ∧
      |deriv (deriv Real.smoothTransition) x| ≤ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«smoothTransition_deriv_bound» := P2M_GroundTheory_Heights__Heights_smoothTransition_deriv_bound_7ff97014ece1
