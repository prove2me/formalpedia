-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_int_span_norm_ge_7217af94a27b
-- name    : P2M_GroundTheory_Heights__Heights_int_span_norm_ge_7217af94a27b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:01.863953+00:00
-- url     : https://prove2.me/theorems/b4724d00-0483-4289-ae4b-499345b1933d
-- title:
--   P2 M Ground Theory Heights  Heights int span norm ge 7217af94a27b: P2 M Ground Theory Heights  Heights int span norm ge 7217af94a27b
-- statement:
--   The P2 M Ground Theory Heights  Heights int span norm ge 7217af94a27b construction uses the P2 M Ground Theory Heights  Heights int span norm ge 7217af94a27b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L245-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L245-L250

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_int_span_norm_ge_7217af94a27b (x : ℝ) (hx : x ∈ Submodule.span ℤ ({1} : Set ℝ)) (h0 : x ≠ 0) :
    Real.exp (-0) ≤ ‖x‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«int_span_norm_ge» := P2M_GroundTheory_Heights__Heights_int_span_norm_ge_7217af94a27b
