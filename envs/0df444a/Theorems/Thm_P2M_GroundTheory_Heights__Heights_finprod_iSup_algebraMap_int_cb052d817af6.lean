-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_int_cb052d817af6
-- name    : P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_int_cb052d817af6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:31.173275+00:00
-- url     : https://prove2.me/theorems/91d49c40-050d-4008-8bc5-e62620c339a5
-- title:
--   P2 M Ground Theory Heights  Heights finprod i Sup algebra Map int cb052d817af6: P2 M Ground Theory Heights  Heights finprod i Sup algebra Map int cb052d817af6
-- statement:
--   The P2 M Ground Theory Heights  Heights finprod i Sup algebra Map int cb052d817af6 construction uses the P2 M Ground Theory Heights  Heights finprod i Sup algebra Map int cb052d817af6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L30-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L30-L57

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

theorem P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_int_cb052d817af6 {ι : Type*} [Finite ι] {y : ι → 𝓞 K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i)) ^ finrank K L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finprod_iSup_algebraMap_int» := P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_int_cb052d817af6
