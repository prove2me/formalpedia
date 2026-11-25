-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_leviSec_1189e0f84af6
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_leviSec_1189e0f84af6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:30.077733+00:00
-- url     : https://prove2.me/theorems/c08ceb83-a10f-4d77-af03-7dd4437e8cc7
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi eq levi Sec 1189e0f84af6: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi eq levi Sec 1189e0f84af6
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi eq levi Sec 1189e0f84af6 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi eq levi Sec 1189e0f84af6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L238-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L238-L244

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_leviSec_1189e0f84af6 {G : Matrix ι ι ℂ} {m : Matrix κ κ ℂ} (hGX : G *ᵥ X = X) (hGY : G *ᵥ Y = Y)
    (hGB : G * B = B * m) : G = leviSec H B m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«eq_leviSec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_leviSec_1189e0f84af6
