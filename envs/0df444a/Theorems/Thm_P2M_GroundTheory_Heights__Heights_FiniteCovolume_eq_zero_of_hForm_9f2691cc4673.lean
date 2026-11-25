-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_hForm_9f2691cc4673
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_hForm_9f2691cc4673
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:00.428678+00:00
-- url     : https://prove2.me/theorems/9e74a651-cbe8-4ffd-b40f-80f88d4df380
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume eq zero of h Form 9f2691cc4673: P2 M Ground Theory Heights  Heights Finite Covolume eq zero of h Form 9f2691cc4673
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume eq zero of h Form 9f2691cc4673 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume eq zero of h Form 9f2691cc4673 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L78-L88

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
variable (H : Matrix ι ι ℂ)
variable [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_hForm_9f2691cc4673 {H : Matrix ι ι ℂ} (hd : IsUnit H.det) {u : ι → ℂ}
    (hu : ∀ z, hForm H u z = 0) : u = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«eq_zero_of_hForm» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_hForm_9f2691cc4673
