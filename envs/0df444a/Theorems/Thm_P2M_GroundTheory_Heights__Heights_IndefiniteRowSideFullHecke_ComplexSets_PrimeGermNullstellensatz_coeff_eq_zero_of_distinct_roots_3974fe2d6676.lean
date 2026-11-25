-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_coeff_eq_zero_of_distinct_roots_3974fe2d6676
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_coeff_eq_zero_of_distinct_roots_3974fe2d6676
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:28.309155+00:00
-- url     : https://prove2.me/theorems/28299e62-9b4f-4788-87af-78effb68dbdf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Prime Germ Nullstellensatz coeff eq zero of distinct roots 3974fe2d6676: P2 M Ground Theory Heights  Heights Indefinite
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Prime Germ Nullstellensatz coeff eq zero of distinct roots 3974fe2d6676 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Prime Germ Nullstellensatz coeff eq zero of distinct roots 3974fe2d6676 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermNullstellensatz.lean#L67-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermNullstellensatz.lean#L67-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermCanonicalCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermNullstellensatz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz
variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_coeff_eq_zero_of_distinct_roots_3974fe2d6676 {N : ℕ} (c t : Fin N → ℂ) (ht : Function.Injective t)
    (hroot : ∀ m, ∑ j, c j * t m ^ (j : ℕ) = 0) : ∀ j, c j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PrimeGermNullstellensatz».«coeff_eq_zero_of_distinct_roots» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_coeff_eq_zero_of_distinct_roots_3974fe2d6676
