-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_mirabolicDelta_ne_zero_ad2050164ceb
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_mirabolicDelta_ne_zero_ad2050164ceb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:28.028096+00:00
-- url     : https://prove2.me/theorems/f277907e-991e-48df-a51c-1acfe2a4f3ba
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL mirabolic Delta ne zero ad2050164ceb: P2 M Ground Theory Heights  Theta Fin GL mirabolic Delta ne zero ad2050164ceb
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL mirabolic Delta ne zero ad2050164ceb construction uses the P2 M Ground Theory Heights  Theta Fin GL mirabolic Delta ne zero ad2050164ceb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L351-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L351-L358

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
variable [NeZero n]

theorem P2M_GroundTheory_Heights__Theta_FinGL_mirabolicDelta_ne_zero_ad2050164ceb (ψ₀ : AddChar F ℂ) : mirabolicDelta n F ψ₀ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«mirabolicDelta_ne_zero» := P2M_GroundTheory_Heights__Theta_FinGL_mirabolicDelta_ne_zero_ad2050164ceb
