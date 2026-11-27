-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_top_mem_fullChain_152a1f1100f1
-- name    : P2M_GroundTheory_Heights__Theta_top_mem_fullChain_152a1f1100f1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:25.796924+00:00
-- url     : https://prove2.me/theorems/6e0113ed-6c44-406a-aadf-c4b9fd99b34b
-- title:
--   P2 M Ground Theory Heights  Theta top mem full Chain 152a1f1100f1: P2 M Ground Theory Heights  Theta top mem full Chain 152a1f1100f1
-- statement:
--   The P2 M Ground Theory Heights  Theta top mem full Chain 152a1f1100f1 construction uses the P2 M Ground Theory Heights  Theta top mem full Chain 152a1f1100f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L217-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L217-L218

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

theorem P2M_GroundTheory_Heights__Theta_top_mem_fullChain_152a1f1100f1 (𝒲 : IsotropicFlag K H) : ⊤ ∈ fullChain 𝒲 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«top_mem_fullChain» := P2M_GroundTheory_Heights__Theta_top_mem_fullChain_152a1f1100f1
