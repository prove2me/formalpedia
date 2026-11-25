-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_finset_span_integral_of_div_cb55b2e17947
-- name    : P2M_GroundTheory_Heights__Heights_exists_finset_span_integral_of_div_cb55b2e17947
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:06:52.72706+00:00
-- url     : https://prove2.me/theorems/d9f704a5-bdab-46ca-8df1-c01ee1752911
-- title:
--   P2 M Ground Theory Heights  Heights exists finset span integral of div cb55b2e17947: P2 M Ground Theory Heights  Heights exists finset span integral of div cb55b2e17947
-- statement:
--   The P2 M Ground Theory Heights  Heights exists finset span integral of div cb55b2e17947 construction uses the P2 M Ground Theory Heights  Heights exists finset span integral of div cb55b2e17947 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L12-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L12-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
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
open MvPolynomial ComplexSets FieldNumbers
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_exists_finset_span_integral_of_div_cb55b2e17947 (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O Ω : Type}
    [CommRing O] [Field Ω] [Algebra O Ω] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f)
    (hΩ : ∀ x : Ω, ∃ a b : O, x = algebraMap O Ω a / algebraMap O Ω b) :
    ∃ t : Finset Ω, ∀ x : Ω, IsIntegral O x → x ∈ Submodule.span O (t : Set Ω) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_finset_span_integral_of_div» := P2M_GroundTheory_Heights__Heights_exists_finset_span_integral_of_div_cb55b2e17947
