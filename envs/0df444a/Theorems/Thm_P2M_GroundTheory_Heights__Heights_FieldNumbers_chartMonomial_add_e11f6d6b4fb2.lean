-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_add_e11f6d6b4fb2
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_add_e11f6d6b4fb2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:05:11.509231+00:00
-- url     : https://prove2.me/theorems/63ed5840-8922-5bd6-8b9a-f2d6a584b375
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers chart Monomial add e11f6d6b4fb2: P2 M Ground Theory Heights  Heights Field Numbers chart Monomial add e11f6d6b4fb2
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers chart Monomial add e11f6d6b4fb2 construction uses the P2 M Ground Theory Heights  Heights Field Numbers chart Monomial add e11f6d6b4fb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartHomog
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_add_e11f6d6b4fb2 (u : ∀ k, ι k) (a c : K → ℕ) :
    (chartMonomial u (a + c) : MRing ι F) = chartMonomial u a * chartMonomial u c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«chartMonomial_add» := P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_add_e11f6d6b4fb2
