-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_bot_mem_fullChain_11f5dee2f33c
-- name    : P2M_GroundTheory_Heights__Theta_bot_mem_fullChain_11f5dee2f33c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:21.021559+00:00
-- url     : https://prove2.me/theorems/1a3c1bb6-2155-484d-b3c8-3fc01e9a225d
-- title:
--   P2 M Ground Theory Heights  Theta bot mem full Chain 11f5dee2f33c: P2 M Ground Theory Heights  Theta bot mem full Chain 11f5dee2f33c
-- statement:
--   The P2 M Ground Theory Heights  Theta bot mem full Chain 11f5dee2f33c construction uses the P2 M Ground Theory Heights  Theta bot mem full Chain 11f5dee2f33c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L214-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L214-L215

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

theorem P2M_GroundTheory_Heights__Theta_bot_mem_fullChain_11f5dee2f33c (𝒲 : IsotropicFlag K H) : ⊥ ∈ fullChain 𝒲 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«bot_mem_fullChain» := P2M_GroundTheory_Heights__Theta_bot_mem_fullChain_11f5dee2f33c
