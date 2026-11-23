-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_left_c137c8023bfd
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_left_c137c8023bfd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:51.028669+00:00
-- url     : https://prove2.me/theorems/805d6920-fcad-4435-a1fa-849b95feae93
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip B left c137c8023bfd: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip B left c137c8023bfd
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip B left c137c8023bfd construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip B left c137c8023bfd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L137-L139

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_left_c137c8023bfd (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) (c : κ → ℂ) :
    star (B *ᵥ c) ⬝ᵥ (H *ᵥ X) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«ip_B_left» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_left_c137c8023bfd
