-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_Flag_ofSubspace_isProper_8f7bad3b45ee
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_Flag_ofSubspace_isProper_8f7bad3b45ee
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:23.868447+00:00
-- url     : https://prove2.me/theorems/75a69e0a-1c0c-44bb-a860-75f9ca1160cb
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL Flag of Subspace is Proper 8f7bad3b45ee: P2 M Ground Theory Heights  Theta Fin GL Flag of Subspace is Proper 8f7bad3b45ee
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL Flag of Subspace is Proper 8f7bad3b45ee construction uses the P2 M Ground Theory Heights  Theta Fin GL Flag of Subspace is Proper 8f7bad3b45ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L253-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L253-L255

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

theorem P2M_GroundTheory_Heights__Theta_FinGL_Flag_ofSubspace_isProper_8f7bad3b45ee {W : Submodule F (Fin n → F)} (h0 : W ≠ ⊥) (h1 : W ≠ ⊤) :
    (Flag.ofSubspace W).IsProper := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«Flag».«ofSubspace_isProper» := P2M_GroundTheory_Heights__Theta_FinGL_Flag_ofSubspace_isProper_8f7bad3b45ee
