-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_fracMap_unit_ede7a277c87b
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_fracMap_unit_ede7a277c87b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:24:20.11371+00:00
-- url     : https://prove2.me/theorems/76d4e7d2-4920-548c-8400-1af90359b81e
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place exists frac Map unit ede7a277c87b: P2 M Ground Theory Heights  Heights Minimal Prime Place exists frac Map unit ede7a277c87b
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place exists frac Map unit ede7a277c87b construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place exists frac Map unit ede7a277c87b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L79-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L79-L131

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

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_fracMap_unit_ede7a277c87b [IsNoetherianRing A] [IsReduced A] [IsDomain B] (π : A →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π ∈ minimalPrimes A) :
    ∃ e : FractionRing A, fracMap π hker e = 1 ∧ (∀ z, fracMap π hker z = 0 → e * z = 0) ∧
      ∀ y : FractionRing B, ∃ x, fracMap π hker x = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«exists_fracMap_unit» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_fracMap_unit_ede7a277c87b
