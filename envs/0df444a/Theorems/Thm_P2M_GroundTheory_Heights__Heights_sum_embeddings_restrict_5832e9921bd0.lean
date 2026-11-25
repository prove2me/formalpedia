-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_embeddings_restrict_5832e9921bd0
-- name    : P2M_GroundTheory_Heights__Heights_sum_embeddings_restrict_5832e9921bd0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:04:24.553849+00:00
-- url     : https://prove2.me/theorems/e917d5bd-da6b-4321-9674-f859728750c7
-- title:
--   P2 M Ground Theory Heights  Heights sum embeddings restrict 5832e9921bd0: P2 M Ground Theory Heights  Heights sum embeddings restrict 5832e9921bd0
-- statement:
--   The P2 M Ground Theory Heights  Heights sum embeddings restrict 5832e9921bd0 construction uses the P2 M Ground Theory Heights  Heights sum embeddings restrict 5832e9921bd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L22-L28

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

theorem P2M_GroundTheory_Heights__Heights_sum_embeddings_restrict_5832e9921bd0 (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = finrank K L * ∑ τ : K →+* ℂ, f τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_embeddings_restrict» := P2M_GroundTheory_Heights__Heights_sum_embeddings_restrict_5832e9921bd0
