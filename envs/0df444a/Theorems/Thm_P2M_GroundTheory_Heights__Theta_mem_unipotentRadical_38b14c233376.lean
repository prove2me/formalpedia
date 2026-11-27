-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_mem_unipotentRadical_38b14c233376
-- name    : P2M_GroundTheory_Heights__Theta_mem_unipotentRadical_38b14c233376
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:54.925872+00:00
-- url     : https://prove2.me/theorems/771d02a9-cedc-46b7-a7ad-346b4551fd7f
-- title:
--   P2 M Ground Theory Heights  Theta mem unipotent Radical 38b14c233376: P2 M Ground Theory Heights  Theta mem unipotent Radical 38b14c233376
-- statement:
--   The P2 M Ground Theory Heights  Theta mem unipotent Radical 38b14c233376 construction uses the P2 M Ground Theory Heights  Theta mem unipotent Radical 38b14c233376 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L368-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L368-L372

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

theorem P2M_GroundTheory_Heights__Theta_mem_unipotentRadical_38b14c233376 {𝒲 : IsotropicFlag K H} {g : unitaryPoints K E H R} :
    g ∈ unipotentRadical H R 𝒲 ↔ ∀ B ∈ fullChain 𝒲, ∀ x ∈ extendScalars K R B,
      unitaryMat g *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) ∧
      unitaryMat g⁻¹ *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«mem_unipotentRadical» := P2M_GroundTheory_Heights__Theta_mem_unipotentRadical_38b14c233376
