-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_ord_eq_ord_polynomial_bd5f17fea660
-- name    : P2M_GroundTheory_Heights__Heights_exists_ord_eq_ord_polynomial_bd5f17fea660
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:34.076181+00:00
-- url     : https://prove2.me/theorems/92e74f66-e326-4213-82a1-32abc82b0f65
-- title:
--   P2 M Ground Theory Heights  Heights exists ord eq ord polynomial bd5f17fea660: P2 M Ground Theory Heights  Heights exists ord eq ord polynomial bd5f17fea660
-- statement:
--   The P2 M Ground Theory Heights  Heights exists ord eq ord polynomial bd5f17fea660 construction uses the P2 M Ground Theory Heights  Heights exists ord eq ord polynomial bd5f17fea660 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/POrdDeterminesPlace.lean#L25-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/POrdDeterminesPlace.lean#L25-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdDeterminesPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdDeterminesPlace
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

theorem P2M_GroundTheory_Heights__Heights_exists_ord_eq_ord_polynomial_bd5f17fea660 (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (a : curveLocalRing I q) : ∃ f : MvPolynomial (Fin n) ℂ, ∀ P : MaximalSpectrum (curveNormalisation I q),
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_ord_eq_ord_polynomial» := P2M_GroundTheory_Heights__Heights_exists_ord_eq_ord_polynomial_bd5f17fea660
