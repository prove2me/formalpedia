-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinExists_continuous_qf_a86f9130f63a
-- name    : P2M_GroundTheory_Heights__Heights_PSymplMinExists_continuous_qf_a86f9130f63a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:23.087923+00:00
-- url     : https://prove2.me/theorems/2cce433a-404b-45ad-9b5d-c197e05a61d4
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Min Exists continuous qf a86f9130f63a: P2 M Ground Theory Heights  Heights PSympl Min Exists continuous qf a86f9130f63a
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Min Exists continuous qf a86f9130f63a construction uses the P2 M Ground Theory Heights  Heights PSympl Min Exists continuous qf a86f9130f63a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinExists.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinExists.lean#L17-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.PSymplMinExists
variable {ι : Type} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_PSymplMinExists_continuous_qf_a86f9130f63a (G : Matrix ι ι ℝ) : Continuous (qf G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplMinExists».«continuous_qf» := P2M_GroundTheory_Heights__Heights_PSymplMinExists_continuous_qf_a86f9130f63a
