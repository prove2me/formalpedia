-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_finiteTerm_algebraMap_b2a1b9f5b23a
-- name    : P2M_GroundTheory_Heights__Heights_finsum_finiteTerm_algebraMap_b2a1b9f5b23a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:04:55.15415+00:00
-- url     : https://prove2.me/theorems/a49ca78d-b3c6-429c-ad9b-f8ad2c4127fc
-- title:
--   P2 M Ground Theory Heights  Heights finsum finite Term algebra Map b2a1b9f5b23a: P2 M Ground Theory Heights  Heights finsum finite Term algebra Map b2a1b9f5b23a
-- statement:
--   The P2 M Ground Theory Heights  Heights finsum finite Term algebra Map b2a1b9f5b23a construction uses the P2 M Ground Theory Heights  Heights finsum finite Term algebra Map b2a1b9f5b23a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L178-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L178-L190

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_finsum_finiteTerm_algebraMap_b2a1b9f5b23a {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (A : HermLine n) {y : Cone n K} (hy : BlockNonzero y) :
    ∑ᶠ w : FinitePlace L, finiteTerm A w (fun k i ↦ algebraMap K L (y k i)) =
      finrank K L * ∑ᶠ v : FinitePlace K, finiteTerm A v y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finsum_finiteTerm_algebraMap» := P2M_GroundTheory_Heights__Heights_finsum_finiteTerm_algebraMap_b2a1b9f5b23a
