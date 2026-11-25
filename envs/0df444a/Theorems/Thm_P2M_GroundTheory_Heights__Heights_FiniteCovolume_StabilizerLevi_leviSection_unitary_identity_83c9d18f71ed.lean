-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSection_unitary_identity_83c9d18f71ed
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSection_unitary_identity_83c9d18f71ed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:32.276924+00:00
-- url     : https://prove2.me/theorems/02f88371-a15a-5ff7-b09f-d0ab4f828708
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Section unitary identity 83c9d18f71ed: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Section unitary
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Section unitary identity 83c9d18f71ed construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Section unitary identity 83c9d18f71ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L100-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L100-L122

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
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSection_unitary_identity_83c9d18f71ed (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ)
    (hm : mᴴ * (Bᴴ * H * B) * m = Bᴴ * H * B) :
    (leviSec H B m)ᴴ * H * leviSec H B m =
      (1 - B * leftInv H B)ᴴ * (H * (1 - B * leftInv H B)) +
        (leftInv H B)ᴴ * (Bᴴ * (H * (B * leftInv H B))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«leviSection_unitary_identity» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSection_unitary_identity_83c9d18f71ed
