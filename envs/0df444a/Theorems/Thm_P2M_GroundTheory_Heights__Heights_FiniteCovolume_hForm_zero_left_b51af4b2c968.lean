-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_left_b51af4b2c968
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_left_b51af4b2c968
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:14.749737+00:00
-- url     : https://prove2.me/theorems/76d94484-257b-5c73-ba59-289da6ed376e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form zero left b51af4b2c968: P2 M Ground Theory Heights  Heights Finite Covolume h Form zero left b51af4b2c968
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form zero left b51af4b2c968 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form zero left b51af4b2c968 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L42-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L42-L42

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_left_b51af4b2c968 (z : ι → ℂ) : hForm H 0 z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_zero_left» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_left_b51af4b2c968
