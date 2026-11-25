-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_genericChar_upperTwo_67efdcaf75fa
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_genericChar_upperTwo_67efdcaf75fa
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:57.763125+00:00
-- url     : https://prove2.me/theorems/3b58170b-55c4-5cfe-ba1a-ee52fb1c7ed5
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL generic Char upper Two 67efdcaf75fa: P2 M Ground Theory Heights  Theta Fin GL generic Char upper Two 67efdcaf75fa
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL generic Char upper Two 67efdcaf75fa construction uses the P2 M Ground Theory Heights  Theta Fin GL generic Char upper Two 67efdcaf75fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L309-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L309-L311

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

theorem P2M_GroundTheory_Heights__Theta_FinGL_genericChar_upperTwo_67efdcaf75fa (ψ₀ : AddChar F ℂ) (x : F) :
    genericChar 2 F ψ₀ ⟨upperTwo x, upperTwo_mem x⟩ = ψ₀ x := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«genericChar_upperTwo» := P2M_GroundTheory_Heights__Theta_FinGL_genericChar_upperTwo_67efdcaf75fa
