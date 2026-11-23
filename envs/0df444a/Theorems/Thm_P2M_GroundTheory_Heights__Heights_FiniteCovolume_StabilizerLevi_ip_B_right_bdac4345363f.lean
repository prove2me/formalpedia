-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_right_bdac4345363f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_right_bdac4345363f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:39.139182+00:00
-- url     : https://prove2.me/theorems/79991697-4138-4608-957f-0516bafd90f3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip B right bdac4345363f: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip B right bdac4345363f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip B right bdac4345363f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip B right bdac4345363f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L141-L143

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_right_bdac4345363f (hH : Hᴴ = H) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) (c : κ → ℂ) :
    star X ⬝ᵥ (H *ᵥ (B *ᵥ c)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«ip_B_right» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_right_bdac4345363f
