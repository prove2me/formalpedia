-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_6de04aaeab4a
-- name    : P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_6de04aaeab4a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:41.776033+00:00
-- url     : https://prove2.me/theorems/d7185356-b871-44c4-9a6a-3695b4dc02a0
-- title:
--   P2 M Ground Theory Heights  Heights finprod i Sup algebra Map 6de04aaeab4a: P2 M Ground Theory Heights  Heights finprod i Sup algebra Map 6de04aaeab4a
-- statement:
--   The P2 M Ground Theory Heights  Heights finprod i Sup algebra Map 6de04aaeab4a construction uses the P2 M Ground Theory Heights  Heights finprod i Sup algebra Map 6de04aaeab4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L77-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L77-L115

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

theorem P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_6de04aaeab4a {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i)) ^ finrank K L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finprod_iSup_algebraMap» := P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_6de04aaeab4a
