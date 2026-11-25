-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_isMultiHomog_f53a5f857a85
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_isMultiHomog_f53a5f857a85
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:44.583295+00:00
-- url     : https://prove2.me/theorems/3cdda41c-c217-4cd0-a13d-05f3971caa59
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers chart Monomial is Multi Homog f53a5f857a85: P2 M Ground Theory Heights  Heights Field Numbers chart Monomial is Multi Homog f53a5f857a85
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers chart Monomial is Multi Homog f53a5f857a85 construction uses the P2 M Ground Theory Heights  Heights Field Numbers chart Monomial is Multi Homog f53a5f857a85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L21-L29

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_isMultiHomog_f53a5f857a85 (u : ∀ k, ι k) (c : K → ℕ) :
    IsMultiHomog (chartMonomial u c : MRing ι F) c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«chartMonomial_isMultiHomog» := P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_isMultiHomog_f53a5f857a85
