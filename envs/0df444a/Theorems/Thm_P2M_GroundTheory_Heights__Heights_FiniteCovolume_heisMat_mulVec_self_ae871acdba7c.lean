-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_self_ae871acdba7c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_self_ae871acdba7c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:28.533175+00:00
-- url     : https://prove2.me/theorems/4cb0a9b8-d257-54ec-a8ca-9416519766dc
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul Vec self ae871acdba7c: P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul Vec self ae871acdba7c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul Vec self ae871acdba7c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul Vec self ae871acdba7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L144-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L144-L148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_self_ae871acdba7c {y : ι → ℂ} (hy : hForm H a y = 0) (s : ℂ) :
    heisMat H a y s *ᵥ a = a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisMat_mulVec_self» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_self_ae871acdba7c
