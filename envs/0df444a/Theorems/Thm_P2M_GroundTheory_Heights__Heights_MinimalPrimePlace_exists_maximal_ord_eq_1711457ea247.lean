-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_maximal_ord_eq_1711457ea247
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_maximal_ord_eq_1711457ea247
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:04:03.802904+00:00
-- url     : https://prove2.me/theorems/da46f101-c8e7-41fc-9989-46cf838bce55
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place exists maximal ord eq 1711457ea247: P2 M Ground Theory Heights  Heights Minimal Prime Place exists maximal ord eq 1711457ea247
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place exists maximal ord eq 1711457ea247 construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place exists maximal ord eq 1711457ea247 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L196-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L196-L221

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
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
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_maximal_ord_eq_1711457ea247 [IsNoetherianRing A] [IsReduced A] [IsDomain B] (π : A →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π ∈ minimalPrimes A)
    (P' : MaximalSpectrum (integralClosure B (FractionRing B))) :
    ∃ P : MaximalSpectrum (integralClosure A (FractionRing A)), ∀ a : A,
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap _ (Localization.AtPrime P.asIdeal) (algebraMap A (integralClosure A (FractionRing A)) a)) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap _ (Localization.AtPrime P'.asIdeal) (algebraMap B (integralClosure B (FractionRing B)) (π a))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«exists_maximal_ord_eq» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_maximal_ord_eq_1711457ea247
