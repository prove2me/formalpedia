-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_mulVec_leftInv_of_8284feb2c2cd
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_mulVec_leftInv_of_8284feb2c2cd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:48.075144+00:00
-- url     : https://prove2.me/theorems/d90fb8d4-c7a1-4142-b023-418b992140a3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi mul Vec left Inv of 8284feb2c2cd: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi mul Vec left Inv of 8284feb2c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi mul Vec left Inv of 8284feb2c2cd construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi mul Vec left Inv of 8284feb2c2cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L165-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {X Y : ι → ℂ}
variable (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0)
    (hBY : Bᴴ *ᵥ (H *ᵥ Y) = 0) (hXX : star X ⬝ᵥ (H *ᵥ X) = 0) (hYY : star Y ⬝ᵥ (H *ᵥ Y) = 0)
    (hXY : star X ⬝ᵥ (H *ᵥ Y) = 1) (hspan : ∀ z, ∃ (a b : ℂ) (c : κ → ℂ), z = a • X + b • Y + B *ᵥ c)
include hH hG hBX hBY hXX hYY hXY hspan

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_mulVec_leftInv_of_8284feb2c2cd (z : ι → ℂ) (hz : star X ⬝ᵥ (H *ᵥ z) = 0) :
    B *ᵥ (leftInv H B *ᵥ z) = z - (star Y ⬝ᵥ (H *ᵥ z)) • X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«mulVec_leftInv_of» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_mulVec_leftInv_of_8284feb2c2cd
