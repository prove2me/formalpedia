-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_unipotentRadical_le_parabolic_6bf8b111b773
-- name    : P2M_GroundTheory_Heights__Theta_unipotentRadical_le_parabolic_6bf8b111b773
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:37.410998+00:00
-- url     : https://prove2.me/theorems/05451903-b8fb-4a75-a72d-d10533159398
-- title:
--   P2 M Ground Theory Heights  Theta unipotent Radical le parabolic 6bf8b111b773: P2 M Ground Theory Heights  Theta unipotent Radical le parabolic 6bf8b111b773
-- statement:
--   The P2 M Ground Theory Heights  Theta unipotent Radical le parabolic 6bf8b111b773 construction uses the P2 M Ground Theory Heights  Theta unipotent Radical le parabolic 6bf8b111b773 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L374-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L374-L381

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
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R]

theorem P2M_GroundTheory_Heights__Theta_unipotentRadical_le_parabolic_6bf8b111b773 (𝒲 : IsotropicFlag K H) :
    unipotentRadical H R 𝒲 ≤ parabolic H R 𝒲 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«unipotentRadical_le_parabolic» := P2M_GroundTheory_Heights__Theta_unipotentRadical_le_parabolic_6bf8b111b773
