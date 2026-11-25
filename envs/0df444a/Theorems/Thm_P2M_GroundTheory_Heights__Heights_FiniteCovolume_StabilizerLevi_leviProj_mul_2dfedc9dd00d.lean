-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_mul_2dfedc9dd00d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_mul_2dfedc9dd00d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:40.780624+00:00
-- url     : https://prove2.me/theorems/e63dec5c-fd84-4276-b33f-5760d8ac1670
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Proj mul 2dfedc9dd00d: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Proj mul 2dfedc9dd00d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Proj mul 2dfedc9dd00d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Proj mul 2dfedc9dd00d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L177-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L177-L186

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_mul_2dfedc9dd00d {g g' : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X)
    (hg' : g'ᴴ * H * g' = H) (hgX' : g' *ᵥ X = X) :
    leviProj H B (g * g') = leviProj H B g * leviProj H B g' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«leviProj_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_mul_2dfedc9dd00d
