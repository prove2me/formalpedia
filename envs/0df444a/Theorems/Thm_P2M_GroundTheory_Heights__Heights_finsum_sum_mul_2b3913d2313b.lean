-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_sum_mul_2b3913d2313b
-- name    : P2M_GroundTheory_Heights__Heights_finsum_sum_mul_2b3913d2313b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:34.143236+00:00
-- url     : https://prove2.me/theorems/36c27734-6b9b-4536-8634-1170a7bac3c4
-- title:
--   P2 M Ground Theory Heights  Heights finsum sum mul 2b3913d2313b: P2 M Ground Theory Heights  Heights finsum sum mul 2b3913d2313b
-- statement:
--   The P2 M Ground Theory Heights  Heights finsum sum mul 2b3913d2313b construction uses the P2 M Ground Theory Heights  Heights finsum sum mul 2b3913d2313b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L147-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L147-L162

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

theorem P2M_GroundTheory_Heights__Heights_finsum_sum_mul_2b3913d2313b {α ι : Type*} [Fintype ι] (c : ι → ℝ) (g : ι → α → ℝ)
    (hg : ∀ k, (Function.support (g k)).Finite) :
    ∑ᶠ a, ∑ k, c k * g k a = ∑ k, c k * ∑ᶠ a, g k a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finsum_sum_mul» := P2M_GroundTheory_Heights__Heights_finsum_sum_mul_2b3913d2313b
