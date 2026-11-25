-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_zero_6a323343603e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_zero_6a323343603e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:36.285654+00:00
-- url     : https://prove2.me/theorems/adfcbc62-6d44-4ef2-a2ac-466ffca3f11d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Mat zero 6a323343603e: P2 M Ground Theory Heights  Heights Finite Covolume heis Mat zero 6a323343603e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Mat zero 6a323343603e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Mat zero 6a323343603e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L138-L139

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_zero_6a323343603e : heisMat H a 0 0 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisMat_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_zero_6a323343603e
