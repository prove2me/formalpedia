-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_card_embeddings_restrict_a19e8def3342
-- name    : P2M_GroundTheory_Heights__Heights_card_embeddings_restrict_a19e8def3342
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:05:32.787145+00:00
-- url     : https://prove2.me/theorems/6d4bbf7d-a4ef-4ec1-9098-4e75c5f12209
-- title:
--   P2 M Ground Theory Heights  Heights card embeddings restrict a19e8def3342: P2 M Ground Theory Heights  Heights card embeddings restrict a19e8def3342
-- statement:
--   The P2 M Ground Theory Heights  Heights card embeddings restrict a19e8def3342 construction uses the P2 M Ground Theory Heights  Heights card embeddings restrict a19e8def3342 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
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
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
open Classical

theorem P2M_GroundTheory_Heights__Heights_card_embeddings_restrict_a19e8def3342 (τ : K →+* ℂ) :
    (Finset.univ.filter fun σ : L →+* ℂ ↦ σ.comp (algebraMap K L) = τ).card = finrank K L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«card_embeddings_restrict» := P2M_GroundTheory_Heights__Heights_card_embeddings_restrict_a19e8def3342
