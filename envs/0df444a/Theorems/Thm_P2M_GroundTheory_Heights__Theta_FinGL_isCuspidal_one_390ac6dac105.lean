-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_isCuspidal_one_390ac6dac105
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_isCuspidal_one_390ac6dac105
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:08.493171+00:00
-- url     : https://prove2.me/theorems/2c721ec7-3da6-5d0b-b17f-61ff182224b4
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL is Cuspidal one 390ac6dac105: P2 M Ground Theory Heights  Theta Fin GL is Cuspidal one 390ac6dac105
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL is Cuspidal one 390ac6dac105 construction uses the P2 M Ground Theory Heights  Theta Fin GL is Cuspidal one 390ac6dac105 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L285-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L285-L287

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

theorem P2M_GroundTheory_Heights__Theta_FinGL_isCuspidal_one_390ac6dac105 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 1) F) V) : IsCuspidal 1 F ρ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«isCuspidal_one» := P2M_GroundTheory_Heights__Theta_FinGL_isCuspidal_one_390ac6dac105
