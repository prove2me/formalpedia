-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_neg_left_ff70cfa4a8ef
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_neg_left_ff70cfa4a8ef
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:51.434803+00:00
-- url     : https://prove2.me/theorems/42cc11ef-2660-53fb-941c-0cd5798d3ac3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form neg left ff70cfa4a8ef: P2 M Ground Theory Heights  Heights Finite Covolume h Form neg left ff70cfa4a8ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form neg left ff70cfa4a8ef construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form neg left ff70cfa4a8ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L29-L30

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_neg_left_ff70cfa4a8ef (u z : ι → ℂ) : hForm H (-u) z = -hForm H u z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_neg_left» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_neg_left_ff70cfa4a8ef
