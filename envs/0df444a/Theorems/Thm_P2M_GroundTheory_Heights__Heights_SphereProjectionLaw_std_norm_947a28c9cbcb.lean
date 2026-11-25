-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_std_norm_947a28c9cbcb
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_std_norm_947a28c9cbcb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:09.207811+00:00
-- url     : https://prove2.me/theorems/53350a9e-e550-4d5c-945b-1ad73b8b410c
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law std norm 947a28c9cbcb: P2 M Ground Theory Heights  Heights Sphere Projection Law std norm 947a28c9cbcb
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law std norm 947a28c9cbcb construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law std norm 947a28c9cbcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L34-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_std_norm_947a28c9cbcb (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«std_norm» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_std_norm_947a28c9cbcb
