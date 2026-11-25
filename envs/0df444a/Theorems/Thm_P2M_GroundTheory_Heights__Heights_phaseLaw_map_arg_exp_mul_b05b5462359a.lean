-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_phaseLaw_map_arg_exp_mul_b05b5462359a
-- name    : P2M_GroundTheory_Heights__Heights_phaseLaw_map_arg_exp_mul_b05b5462359a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:35.279746+00:00
-- url     : https://prove2.me/theorems/2bc499b5-8b89-4037-acf6-55ffa26618f5
-- title:
--   P2 M Ground Theory Heights  Heights phase Law map arg exp mul b05b5462359a: P2 M Ground Theory Heights  Heights phase Law map arg exp mul b05b5462359a
-- statement:
--   The P2 M Ground Theory Heights  Heights phase Law map arg exp mul b05b5462359a construction uses the P2 M Ground Theory Heights  Heights phase Law map arg exp mul b05b5462359a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSpherePhase.lean#L12-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSpherePhase.lean#L12-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSpherePhase
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
open MeasureTheory ProbabilityTheory Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_phaseLaw_map_arg_exp_mul_b05b5462359a {c : ℂ} (hc : c ≠ 0) :
    phaseLaw.map (fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * c)) = phaseLaw := by sorry

alias «GroundTheory».«Heights₂».«Heights».«phaseLaw_map_arg_exp_mul» := P2M_GroundTheory_Heights__Heights_phaseLaw_map_arg_exp_mul_b05b5462359a
