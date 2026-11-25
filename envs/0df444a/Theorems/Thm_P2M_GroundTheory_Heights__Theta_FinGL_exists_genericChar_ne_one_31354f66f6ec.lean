-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_exists_genericChar_ne_one_31354f66f6ec
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_exists_genericChar_ne_one_31354f66f6ec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:26.786598+00:00
-- url     : https://prove2.me/theorems/303c03be-54fb-4392-b3fc-c651e8f6d3e6
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL exists generic Char ne one 31354f66f6ec: P2 M Ground Theory Heights  Theta Fin GL exists generic Char ne one 31354f66f6ec
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL exists generic Char ne one 31354f66f6ec construction uses the P2 M Ground Theory Heights  Theta Fin GL exists generic Char ne one 31354f66f6ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L313-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L313-L316

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FinGL
open Matrix
noncomputable section
variable {n : ℕ} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Theta_FinGL_exists_genericChar_ne_one_31354f66f6ec {ψ₀ : AddChar F ℂ} (hψ₀ : ψ₀ ≠ 1) :
    ∃ u, genericChar 2 F ψ₀ u ≠ 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«exists_genericChar_ne_one» := P2M_GroundTheory_Heights__Theta_FinGL_exists_genericChar_ne_one_31354f66f6ec
