-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_toBase_mem_extendScalars_6d939e4090f3
-- name    : P2M_GroundTheory_Heights__Theta_toBase_mem_extendScalars_6d939e4090f3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:21.272582+00:00
-- url     : https://prove2.me/theorems/dfeaf43f-8fe4-4b50-bd6e-be9dd6f07565
-- title:
--   P2 M Ground Theory Heights  Theta to Base mem extend Scalars 6d939e4090f3: P2 M Ground Theory Heights  Theta to Base mem extend Scalars 6d939e4090f3
-- statement:
--   The P2 M Ground Theory Heights  Theta to Base mem extend Scalars 6d939e4090f3 construction uses the P2 M Ground Theory Heights  Theta to Base mem extend Scalars 6d939e4090f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L288-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L288-L290

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
variable (K) (R : Type*) [CommRing R] [Algebra K R]
variable {K R}

theorem P2M_GroundTheory_Heights__Theta_toBase_mem_extendScalars_6d939e4090f3 {W : Submodule E (ι → E)} {x : ι → E} (hx : x ∈ W) :
    toBase K R x ∈ extendScalars K R W := by sorry

alias «GroundTheory».«Heights₂».«Theta».«toBase_mem_extendScalars» := P2M_GroundTheory_Heights__Theta_toBase_mem_extendScalars_6d939e4090f3
