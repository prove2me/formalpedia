-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_right_6b8edb0e313a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_right_6b8edb0e313a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:21.429148+00:00
-- url     : https://prove2.me/theorems/a975f682-cc3b-47c4-8287-63b7bf57f9a4
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form zero right 6b8edb0e313a: P2 M Ground Theory Heights  Heights Finite Covolume h Form zero right 6b8edb0e313a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form zero right 6b8edb0e313a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form zero right 6b8edb0e313a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L44-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L44-L44

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_right_6b8edb0e313a (u : ι → ℂ) : hForm H u 0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_zero_right» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_right_6b8edb0e313a
