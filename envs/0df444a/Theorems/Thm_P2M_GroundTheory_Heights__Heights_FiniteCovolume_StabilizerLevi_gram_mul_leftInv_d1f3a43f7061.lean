-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gram_mul_leftInv_d1f3a43f7061
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gram_mul_leftInv_d1f3a43f7061
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:13.869969+00:00
-- url     : https://prove2.me/theorems/70bdf46d-7a1a-45b1-a474-8d9944607928
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi gram mul left Inv d1f3a43f7061: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi gram mul left Inv d1f3a43f7061
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi gram mul left Inv d1f3a43f7061 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi gram mul left Inv d1f3a43f7061 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L61-L64

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gram_mul_leftInv_d1f3a43f7061 (hG : IsUnit (Bᴴ * H * B).det) :
    Bᴴ * H * B * leftInv H B = Bᴴ * H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«gram_mul_leftInv» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gram_mul_leftInv_d1f3a43f7061
