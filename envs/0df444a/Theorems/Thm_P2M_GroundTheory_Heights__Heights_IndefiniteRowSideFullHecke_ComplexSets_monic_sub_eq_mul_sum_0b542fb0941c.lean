-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_sub_eq_mul_sum_0b542fb0941c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_sub_eq_mul_sum_0b542fb0941c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:18.754799+00:00
-- url     : https://prove2.me/theorems/4be86789-32da-48e4-bbe6-493c5b564e72
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic sub eq mul sum 0b542fb0941c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic sub eq mul sum 0b542fb0941c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic sub eq mul sum 0b542fb0941c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonicDifferenceQuotient.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonicDifferenceQuotient.lean#L28-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient
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
open Finset

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_sub_eq_mul_sum_0b542fb0941c {d : ℕ} (C : Fin d → ℂ) (s t : ℂ) :
    (s ^ d + ∑ k : Fin d, C k * s ^ (k : ℕ)) - (t ^ d + ∑ k : Fin d, C k * t ^ (k : ℕ)) =
      (s - t) * ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«monic_sub_eq_mul_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_sub_eq_mul_sum_0b542fb0941c
