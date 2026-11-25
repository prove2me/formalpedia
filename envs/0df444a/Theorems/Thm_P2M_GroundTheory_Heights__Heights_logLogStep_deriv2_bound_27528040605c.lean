-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogStep_deriv2_bound_27528040605c
-- name    : P2M_GroundTheory_Heights__Heights_logLogStep_deriv2_bound_27528040605c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:32.879925+00:00
-- url     : https://prove2.me/theorems/b9d8bbf5-ea62-40bc-b6b9-9c14911cbd43
-- title:
--   P2 M Ground Theory Heights  Heights log Log Step deriv2 bound 27528040605c: P2 M Ground Theory Heights  Heights log Log Step deriv2 bound 27528040605c
-- statement:
--   The P2 M Ground Theory Heights  Heights log Log Step deriv2 bound 27528040605c construction uses the P2 M Ground Theory Heights  Heights log Log Step deriv2 bound 27528040605c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessDeriv.lean#L76-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessDeriv.lean#L76-L131

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

theorem P2M_GroundTheory_Heights__Heights_logLogStep_deriv2_bound_27528040605c :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ t : ℝ, t < 0 →
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c)) t ∧
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c)) t| ≤ K / (c * t ^ 2) ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t| ≤ K / (c * t ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logLogStep_deriv2_bound» := P2M_GroundTheory_Heights__Heights_logLogStep_deriv2_bound_27528040605c
