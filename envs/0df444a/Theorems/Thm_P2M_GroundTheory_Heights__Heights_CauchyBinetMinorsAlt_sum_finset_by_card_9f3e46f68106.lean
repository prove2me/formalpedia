-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_finset_by_card_9f3e46f68106
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_finset_by_card_9f3e46f68106
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:34.097797+00:00
-- url     : https://prove2.me/theorems/791d1a14-6c7b-4b2a-9ae8-f0afdacef5e1
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt sum finset by card 9f3e46f68106: P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt sum finset by card 9f3e46f68106
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt sum finset by card 9f3e46f68106 construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt sum finset by card 9f3e46f68106 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L29-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors
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
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_finset_by_card_9f3e46f68106 {n : ℕ} {β : Type*} [AddCommMonoid β] (f : Finset (Fin n) → β) :
    ∑ s : Finset (Fin n), f s =
      ∑ k ∈ range (n + 1), ∑ S : {S : Finset (Fin n) // S.card = k}, f S.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetMinorsAlt».«sum_finset_by_card» := P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_finset_by_card_9f3e46f68106
