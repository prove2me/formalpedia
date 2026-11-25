-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_curveLocalRing_eq_div_9ca7f60b5d9b
-- name    : P2M_GroundTheory_Heights__Heights_curveLocalRing_eq_div_9ca7f60b5d9b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:12:45.4858+00:00
-- url     : https://prove2.me/theorems/a00665f6-48c7-5126-a072-df37b4fa4cb7
-- title:
--   P2 M Ground Theory Heights  Heights curve Local Ring eq div 9ca7f60b5d9b: P2 M Ground Theory Heights  Heights curve Local Ring eq div 9ca7f60b5d9b
-- statement:
--   The P2 M Ground Theory Heights  Heights curve Local Ring eq div 9ca7f60b5d9b construction uses the P2 M Ground Theory Heights  Heights curve Local Ring eq div 9ca7f60b5d9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L115-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L115-L127

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

theorem P2M_GroundTheory_Heights__Heights_curveLocalRing_eq_div_9ca7f60b5d9b {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (o : curveLocalRing I q) : ∃ f s, IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s) ∧
      o * algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s =
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«curveLocalRing_eq_div» := P2M_GroundTheory_Heights__Heights_curveLocalRing_eq_div_9ca7f60b5d9b
