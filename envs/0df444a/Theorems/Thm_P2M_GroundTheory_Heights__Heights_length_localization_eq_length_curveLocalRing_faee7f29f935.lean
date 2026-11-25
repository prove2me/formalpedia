-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localization_eq_length_curveLocalRing_faee7f29f935
-- name    : P2M_GroundTheory_Heights__Heights_length_localization_eq_length_curveLocalRing_faee7f29f935
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:18.657046+00:00
-- url     : https://prove2.me/theorems/1c03ed2f-b47a-5bee-8f45-55e9c493cb48
-- title:
--   P2 M Ground Theory Heights  Heights length localization eq length curve Local Ring faee7f29f935: P2 M Ground Theory Heights  Heights length localization eq length curve Local Ring faee7f29f935
-- statement:
--   The P2 M Ground Theory Heights  Heights length localization eq length curve Local Ring faee7f29f935 construction uses the P2 M Ground Theory Heights  Heights length localization eq length curve Local Ring faee7f29f935 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveNormalisationLength.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveNormalisationLength.lean#L26-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StExtensionQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationLength
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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_length_localization_eq_length_curveLocalRing_faee7f29f935 (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    Module.length (Localization.AtPrime (RingHom.ker (eval q)))
        (Localization.AtPrime (RingHom.ker (eval q)) ⧸ (I ⊔ Ideal.span {f}).map
          (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))) =
      Module.length (curveLocalRing I q)
        (curveLocalRing I q ⧸ Ideal.span {algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_localization_eq_length_curveLocalRing» := P2M_GroundTheory_Heights__Heights_length_localization_eq_length_curveLocalRing_faee7f29f935
