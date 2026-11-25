-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_iSup_algebraMap_ec5718db4e82
-- name    : P2M_GroundTheory_Heights__Heights_finsum_log_iSup_algebraMap_ec5718db4e82
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:04:05.889798+00:00
-- url     : https://prove2.me/theorems/08b53306-2bf8-4cc9-b259-6aaf687b9f25
-- title:
--   P2 M Ground Theory Heights  Heights finsum log i Sup algebra Map ec5718db4e82: P2 M Ground Theory Heights  Heights finsum log i Sup algebra Map ec5718db4e82
-- statement:
--   The P2 M Ground Theory Heights  Heights finsum log i Sup algebra Map ec5718db4e82 construction uses the P2 M Ground Theory Heights  Heights finsum log i Sup algebra Map ec5718db4e82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L135-L143

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

theorem P2M_GroundTheory_Heights__Heights_finsum_log_iSup_algebraMap_ec5718db4e82 {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ i, w (algebraMap K L (y i))) =
      finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ i, v (y i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finsum_log_iSup_algebraMap» := P2M_GroundTheory_Heights__Heights_finsum_log_iSup_algebraMap_ec5718db4e82
