-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_chartMonomial_0e5f9b074387
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_chartMonomial_0e5f9b074387
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:43.125841+00:00
-- url     : https://prove2.me/theorems/fd7f1c0d-d3f3-4272-9235-8921a85d687e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog chart Monomial 0e5f9b074387: P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog chart Monomial 0e5f9b074387
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog chart Monomial 0e5f9b074387 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog chart Monomial 0e5f9b074387 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L93-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_chartMonomial_0e5f9b074387 (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isMultiHomog_chartMonomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_chartMonomial_0e5f9b074387
