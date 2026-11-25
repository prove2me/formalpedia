-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_le_orth_of_mem_4c827d4221dd
-- name    : P2M_GroundTheory_Heights__Theta_le_orth_of_mem_4c827d4221dd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:33.345199+00:00
-- url     : https://prove2.me/theorems/cbcdb324-9574-48ca-bc35-1a0d60b85d6f
-- title:
--   P2 M Ground Theory Heights  Theta le orth of mem 4c827d4221dd: P2 M Ground Theory Heights  Theta le orth of mem 4c827d4221dd
-- statement:
--   The P2 M Ground Theory Heights  Theta le orth of mem 4c827d4221dd construction uses the P2 M Ground Theory Heights  Theta le orth of mem 4c827d4221dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L229-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L229-L235

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

theorem P2M_GroundTheory_Heights__Theta_le_orth_of_mem_4c827d4221dd (𝒲 : IsotropicFlag K H) {W W' : Submodule E (ι → E)}
    (hW : W ∈ 𝒲.members) (hW' : W' ∈ 𝒲.members) : W ≤ orth K H W' := by sorry

alias «GroundTheory».«Heights₂».«Theta».«le_orth_of_mem» := P2M_GroundTheory_Heights__Theta_le_orth_of_mem_4c827d4221dd
