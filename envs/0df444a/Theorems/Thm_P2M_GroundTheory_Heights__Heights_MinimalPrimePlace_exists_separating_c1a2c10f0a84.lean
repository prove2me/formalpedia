-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_separating_c1a2c10f0a84
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_separating_c1a2c10f0a84
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:05:28.032804+00:00
-- url     : https://prove2.me/theorems/1de728dd-79d3-5f7a-a435-b061e7322f8b
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place exists separating c1a2c10f0a84: P2 M Ground Theory Heights  Heights Minimal Prime Place exists separating c1a2c10f0a84
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place exists separating c1a2c10f0a84 construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place exists separating c1a2c10f0a84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L36-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L36-L54

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

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_separating_c1a2c10f0a84 [IsNoetherianRing A] {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    ∃ s t : A, t ∈ p ∧ s ∉ p ∧ ∀ q ∈ minimalPrimes A, q ≠ p → s ∈ q ∧ t ∉ q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«exists_separating» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_separating_c1a2c10f0a84
