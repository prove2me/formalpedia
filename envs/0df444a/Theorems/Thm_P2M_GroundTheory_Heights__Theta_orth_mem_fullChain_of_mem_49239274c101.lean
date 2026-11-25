-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_orth_mem_fullChain_of_mem_49239274c101
-- name    : P2M_GroundTheory_Heights__Theta_orth_mem_fullChain_of_mem_49239274c101
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:12.966576+00:00
-- url     : https://prove2.me/theorems/3de4d4df-b0e8-5b0a-8fda-ae2e07b516a1
-- title:
--   P2 M Ground Theory Heights  Theta orth mem full Chain of mem 49239274c101: P2 M Ground Theory Heights  Theta orth mem full Chain of mem 49239274c101
-- statement:
--   The P2 M Ground Theory Heights  Theta orth mem full Chain of mem 49239274c101 construction uses the P2 M Ground Theory Heights  Theta orth mem full Chain of mem 49239274c101 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L224-L227

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

theorem P2M_GroundTheory_Heights__Theta_orth_mem_fullChain_of_mem_49239274c101 {𝒲 : IsotropicFlag K H} {W : Submodule E (ι → E)}
    (hW : W ∈ 𝒲.members) : orth K H W ∈ fullChain 𝒲 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«orth_mem_fullChain_of_mem» := P2M_GroundTheory_Heights__Theta_orth_mem_fullChain_of_mem_49239274c101
