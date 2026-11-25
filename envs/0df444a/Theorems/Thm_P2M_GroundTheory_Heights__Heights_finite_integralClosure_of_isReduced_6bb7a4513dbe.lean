-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_integralClosure_of_isReduced_6bb7a4513dbe
-- name    : P2M_GroundTheory_Heights__Heights_finite_integralClosure_of_isReduced_6bb7a4513dbe
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:21.853115+00:00
-- url     : https://prove2.me/theorems/e72d5125-b23d-563e-944e-dc46a39e7d8a
-- title:
--   P2 M Ground Theory Heights  Heights finite integral Closure of is Reduced 6bb7a4513dbe: P2 M Ground Theory Heights  Heights finite integral Closure of is Reduced 6bb7a4513dbe
-- statement:
--   The P2 M Ground Theory Heights  Heights finite integral Closure of is Reduced 6bb7a4513dbe construction uses the P2 M Ground Theory Heights  Heights finite integral Closure of is Reduced 6bb7a4513dbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L77-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L77-L103

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

theorem P2M_GroundTheory_Heights__Heights_finite_integralClosure_of_isReduced_6bb7a4513dbe (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O : Type}
    [CommRing O] [IsReduced O] [IsNoetherianRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) :
    Module.Finite O (integralClosure O (FractionRing O)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finite_integralClosure_of_isReduced» := P2M_GroundTheory_Heights__Heights_finite_integralClosure_of_isReduced_6bb7a4513dbe
