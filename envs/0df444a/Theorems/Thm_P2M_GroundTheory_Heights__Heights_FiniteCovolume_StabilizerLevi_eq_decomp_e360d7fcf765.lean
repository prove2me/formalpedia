-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_decomp_e360d7fcf765
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_decomp_e360d7fcf765
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:09.040685+00:00
-- url     : https://prove2.me/theorems/de3a6cff-42a6-4fa1-a3c6-140578cc148c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi eq decomp e360d7fcf765: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi eq decomp e360d7fcf765
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi eq decomp e360d7fcf765 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi eq decomp e360d7fcf765 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L145-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L145-L158

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_decomp_e360d7fcf765 (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0)
    (hBY : Bᴴ *ᵥ (H *ᵥ Y) = 0) (hXX : star X ⬝ᵥ (H *ᵥ X) = 0) (hYY : star Y ⬝ᵥ (H *ᵥ Y) = 0)
    (hXY : star X ⬝ᵥ (H *ᵥ Y) = 1) (hspan : ∀ z, ∃ (a b : ℂ) (c : κ → ℂ), z = a • X + b • Y + B *ᵥ c)
    (z : ι → ℂ) :
    z = (star Y ⬝ᵥ (H *ᵥ z)) • X + (star X ⬝ᵥ (H *ᵥ z)) • Y + B *ᵥ (leftInv H B *ᵥ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«eq_decomp» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_decomp_e360d7fcf765
