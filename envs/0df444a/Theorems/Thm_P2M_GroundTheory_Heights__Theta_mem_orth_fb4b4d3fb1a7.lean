-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_mem_orth_fb4b4d3fb1a7
-- name    : P2M_GroundTheory_Heights__Theta_mem_orth_fb4b4d3fb1a7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:13.897117+00:00
-- url     : https://prove2.me/theorems/5cdd15c1-ff18-4ea8-952e-2c1939a69977
-- title:
--   P2 M Ground Theory Heights  Theta mem orth fb4b4d3fb1a7: P2 M Ground Theory Heights  Theta mem orth fb4b4d3fb1a7
-- statement:
--   The P2 M Ground Theory Heights  Theta mem orth fb4b4d3fb1a7 construction uses the P2 M Ground Theory Heights  Theta mem orth fb4b4d3fb1a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L88-L89

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
variable (K H)
variable {K H}

theorem P2M_GroundTheory_Heights__Theta_mem_orth_fb4b4d3fb1a7 {W : Submodule E (ι → E)} {y : ι → E} :
    y ∈ orth K H W ↔ ∀ x ∈ W, hermPair K H x y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«mem_orth» := P2M_GroundTheory_Heights__Theta_mem_orth_fb4b4d3fb1a7
