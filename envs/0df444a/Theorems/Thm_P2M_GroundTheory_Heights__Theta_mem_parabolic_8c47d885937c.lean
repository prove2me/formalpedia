-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_mem_parabolic_8c47d885937c
-- name    : P2M_GroundTheory_Heights__Theta_mem_parabolic_8c47d885937c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:06.34058+00:00
-- url     : https://prove2.me/theorems/6e91e465-d35c-58cc-9d46-71cdf5213a56
-- title:
--   P2 M Ground Theory Heights  Theta mem parabolic 8c47d885937c: P2 M Ground Theory Heights  Theta mem parabolic 8c47d885937c
-- statement:
--   The P2 M Ground Theory Heights  Theta mem parabolic 8c47d885937c construction uses the P2 M Ground Theory Heights  Theta mem parabolic 8c47d885937c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L330-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L330-L333

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
variable {H R}

theorem P2M_GroundTheory_Heights__Theta_mem_parabolic_8c47d885937c {𝒲 : IsotropicFlag K H} {g : unitaryPoints K E H R} :
    g ∈ parabolic H R 𝒲 ↔ ∀ W ∈ 𝒲.members, ∀ x ∈ extendScalars K R W,
      unitaryMat g *ᵥ x ∈ extendScalars K R W ∧ unitaryMat g⁻¹ *ᵥ x ∈ extendScalars K R W := by sorry

alias «GroundTheory».«Heights₂».«Theta».«mem_parabolic» := P2M_GroundTheory_Heights__Theta_mem_parabolic_8c47d885937c
