-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_X_unitary_B_765f6371e569
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_X_unitary_B_765f6371e569
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:42.920007+00:00
-- url     : https://prove2.me/theorems/308bf6c8-6776-4949-a80f-dc859bafb1e6
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip X unitary B 765f6371e569: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip X unitary B 765f6371e569
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip X unitary B 765f6371e569 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip X unitary B 765f6371e569 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L172-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L172-L175

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_X_unitary_B_765f6371e569 {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X) (c : κ → ℂ) :
    star X ⬝ᵥ (H *ᵥ (g *ᵥ (B *ᵥ c))) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«ip_X_unitary_B» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_X_unitary_B_765f6371e569
