-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_eq_zero_of_eventually_const_cf126017d8d7
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_eq_zero_of_eventually_const_cf126017d8d7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:08.8105+00:00
-- url     : https://prove2.me/theorems/bdd1d95c-f224-4dca-9139-c0d64aa7d7f9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers backward Difference eq zero of eventually const cf126017d8d7: P2 M Ground Theory Heights  Heights Field Numbers backward Difference eq zero of eventua
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers backward Difference eq zero of eventually const cf126017d8d7 construction uses the P2 M Ground Theory Heights  Heights Field Numbers backward Difference eq zero of eventually const cf126017d8d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L125-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_eq_zero_of_eventually_const_cf126017d8d7 {g : ℤ → ℤ} {a c : ℤ} (h : ∀ s : ℕ, g (s + a) = c) (s : ℕ) :
    diff1 g (s + (a + 1)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«backwardDifference_eq_zero_of_eventually_const» := P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_eq_zero_of_eventually_const_cf126017d8d7
