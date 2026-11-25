-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finprod_algebraMap_0cb43d4267e7
-- name    : P2M_GroundTheory_Heights__Heights_finprod_algebraMap_0cb43d4267e7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:41.242825+00:00
-- url     : https://prove2.me/theorems/e97f78f6-576b-4da3-b00c-a0afabaeb110
-- title:
--   P2 M Ground Theory Heights  Heights finprod algebra Map 0cb43d4267e7: P2 M Ground Theory Heights  Heights finprod algebra Map 0cb43d4267e7
-- statement:
--   The P2 M Ground Theory Heights  Heights finprod algebra Map 0cb43d4267e7 construction uses the P2 M Ground Theory Heights  Heights finprod algebra Map 0cb43d4267e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L70-L75

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

theorem P2M_GroundTheory_Heights__Heights_finprod_algebraMap_0cb43d4267e7 {c : K} (hc : c ≠ 0) :
    ∏ᶠ w : FinitePlace L, w (algebraMap K L c) = (∏ᶠ v : FinitePlace K, v c) ^ finrank K L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finprod_algebraMap» := P2M_GroundTheory_Heights__Heights_finprod_algebraMap_0cb43d4267e7
