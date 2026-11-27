-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_not_isProper_of_isAnisotropic_5cf04831993b
-- name    : P2M_GroundTheory_Heights__Theta_not_isProper_of_isAnisotropic_5cf04831993b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:09.8728+00:00
-- url     : https://prove2.me/theorems/672eca2b-44b4-5640-968c-a583308c246b
-- title:
--   P2 M Ground Theory Heights  Theta not is Proper of is Anisotropic 5cf04831993b: P2 M Ground Theory Heights  Theta not is Proper of is Anisotropic 5cf04831993b
-- statement:
--   The P2 M Ground Theory Heights  Theta not is Proper of is Anisotropic 5cf04831993b construction uses the P2 M Ground Theory Heights  Theta not is Proper of is Anisotropic 5cf04831993b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L197-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L197-L203

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E)
variable {K H}

theorem P2M_GroundTheory_Heights__Theta_not_isProper_of_isAnisotropic_5cf04831993b (h : IsAnisotropic K H) (𝒲 : IsotropicFlag K H) :
    ¬ 𝒲.IsProper := by sorry

alias «GroundTheory».«Heights₂».«Theta».«not_isProper_of_isAnisotropic» := P2M_GroundTheory_Heights__Theta_not_isProper_of_isAnisotropic_5cf04831993b
