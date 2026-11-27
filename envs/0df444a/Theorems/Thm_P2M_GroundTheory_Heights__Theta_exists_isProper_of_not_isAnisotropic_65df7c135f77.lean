-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_isProper_of_not_isAnisotropic_65df7c135f77
-- name    : P2M_GroundTheory_Heights__Theta_exists_isProper_of_not_isAnisotropic_65df7c135f77
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:04.816949+00:00
-- url     : https://prove2.me/theorems/f2364770-5c33-5c7b-af8b-dc00adc3203f
-- title:
--   P2 M Ground Theory Heights  Theta exists is Proper of not is Anisotropic 65df7c135f77: P2 M Ground Theory Heights  Theta exists is Proper of not is Anisotropic 65df7c135f77
-- statement:
--   The P2 M Ground Theory Heights  Theta exists is Proper of not is Anisotropic 65df7c135f77 construction uses the P2 M Ground Theory Heights  Theta exists is Proper of not is Anisotropic 65df7c135f77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L205-L209

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

theorem P2M_GroundTheory_Heights__Theta_exists_isProper_of_not_isAnisotropic_65df7c135f77 (h : ¬ IsAnisotropic K H) :
    ∃ 𝒲 : IsotropicFlag K H, 𝒲.IsProper := by sorry

alias «GroundTheory».«Heights₂».«Theta».«exists_isProper_of_not_isAnisotropic» := P2M_GroundTheory_Heights__Theta_exists_isProper_of_not_isAnisotropic_65df7c135f77
