-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_left_b196893870d7
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_left_b196893870d7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:14.265256+00:00
-- url     : https://prove2.me/theorems/7a1cf26b-b62a-475a-a676-4dae16ad4d30
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form sub left b196893870d7: P2 M Ground Theory Heights  Heights Finite Covolume h Form sub left b196893870d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form sub left b196893870d7 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form sub left b196893870d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L23-L24

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_left_b196893870d7 (u u' z : ι → ℂ) : hForm H (u - u') z = hForm H u z - hForm H u' z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_sub_left» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_left_b196893870d7
