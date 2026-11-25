-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinExists_qf_smul_c52cc2b03309
-- name    : P2M_GroundTheory_Heights__Heights_PSymplMinExists_qf_smul_c52cc2b03309
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:21.818175+00:00
-- url     : https://prove2.me/theorems/44a02bc5-842b-4d83-8f94-7ff1ca2692f7
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Min Exists qf smul c52cc2b03309: P2 M Ground Theory Heights  Heights PSympl Min Exists qf smul c52cc2b03309
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Min Exists qf smul c52cc2b03309 construction uses the P2 M Ground Theory Heights  Heights PSympl Min Exists qf smul c52cc2b03309 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinExists.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinExists.lean#L13-L15

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

theorem P2M_GroundTheory_Heights__Heights_PSymplMinExists_qf_smul_c52cc2b03309 (G : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) : qf G (c • x) = c ^ 2 * qf G x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplMinExists».«qf_smul» := P2M_GroundTheory_Heights__Heights_PSymplMinExists_qf_smul_c52cc2b03309
