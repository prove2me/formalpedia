-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_unitary_c1fb52bd7931
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_unitary_c1fb52bd7931
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:49.355803+00:00
-- url     : https://prove2.me/theorems/e3a96085-edbf-4654-b897-6e1721747e8a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec unitary c1fb52bd7931: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec unitary c1fb52bd7931
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec unitary c1fb52bd7931 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec unitary c1fb52bd7931 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L124-L129

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_unitary_c1fb52bd7931 (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ)
    (hm : mᴴ * (Bᴴ * H * B) * m = Bᴴ * H * B) :
    (leviSec H B m)ᴴ * H * leviSec H B m = H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«leviSec_unitary» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_unitary_c1fb52bd7931
