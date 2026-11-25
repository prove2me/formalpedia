-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_blockIncl_injective_of_embedding_ab21dab97000
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_blockIncl_injective_of_embedding_ab21dab97000
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:19.923403+00:00
-- url     : https://prove2.me/theorems/01251a5c-df16-4375-a186-47345d4b9344
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted block Incl injective of embedding ab21dab97000: P2 M Ground Theory Heights  Heights Field Numbers PFContracted block Incl injective of em
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted block Incl injective of embedding ab21dab97000 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted block Incl injective of embedding ab21dab97000 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/BlockInclInjectiveOfEmbedding.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/BlockInclInjectiveOfEmbedding.lean#L22-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameHilbFn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRelevantPrimeDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_blockIncl_injective_of_embedding_ab21dab97000 {K K' : Type} (j : K ↪ K') (ι' : K' → Type) :
    Function.Injective (blockIncl j ι') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«blockIncl_injective_of_embedding» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_blockIncl_injective_of_embedding_ab21dab97000
