-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplGramMem_gram_diag_bad6209e6409
-- name    : P2M_GroundTheory_Heights__Heights_PSymplGramMem_gram_diag_bad6209e6409
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:16.875885+00:00
-- url     : https://prove2.me/theorems/442f88e1-d615-4917-8f9a-b5a4fef2ccd4
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Gram Mem gram diag bad6209e6409: P2 M Ground Theory Heights  Heights PSympl Gram Mem gram diag bad6209e6409
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Gram Mem gram diag bad6209e6409 construction uses the P2 M Ground Theory Heights  Heights PSympl Gram Mem gram diag bad6209e6409 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplGramMem.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplGramMem.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplGramMem
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
open GroundTheory.Heights₂.Heights.PSymplGramMem

theorem P2M_GroundTheory_Heights__Heights_PSymplGramMem_gram_diag_bad6209e6409 {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) (x : l) :
    symplGram P G x x = qf G (intVec (P x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplGramMem».«gram_diag» := P2M_GroundTheory_Heights__Heights_PSymplGramMem_gram_diag_bad6209e6409
