-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_extend_mul_a7058f439749
-- name    : P2M_GroundTheory_Heights__Heights_sum_extend_mul_a7058f439749
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:35.873265+00:00
-- url     : https://prove2.me/theorems/f1b946c7-6200-45df-be43-334147d0b679
-- title:
--   P2 M Ground Theory Heights  Heights sum extend mul a7058f439749: P2 M Ground Theory Heights  Heights sum extend mul a7058f439749
-- statement:
--   The P2 M Ground Theory Heights  Heights sum extend mul a7058f439749 construction uses the P2 M Ground Theory Heights  Heights sum extend mul a7058f439749 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L228-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L228-L236

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

theorem P2M_GroundTheory_Heights__Heights_sum_extend_mul_a7058f439749 {ι ι' : Type} [Fintype ι] [Fintype ι'] {j : ι → ι'}
    (hj : Function.Injective j) (a : ι → ℤ) (r : ι' → ℝ) :
    ∑ k', ((Function.extend j a 0 k' : ℤ) : ℝ) * r k' = ∑ k, (a k : ℝ) * r (j k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_extend_mul» := P2M_GroundTheory_Heights__Heights_sum_extend_mul_a7058f439749
