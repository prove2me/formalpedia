-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sub_pow_eq_mul_sum_fin_48c4d365a9ba
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sub_pow_eq_mul_sum_fin_48c4d365a9ba
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:31.033291+00:00
-- url     : https://prove2.me/theorems/45d5100e-5941-586e-8e85-8bf5fb5aabf6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sub pow eq mul sum fin 48c4d365a9ba: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sub
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sub pow eq mul sum fin 48c4d365a9ba construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sub pow eq mul sum fin 48c4d365a9ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonicDifferenceQuotient.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonicDifferenceQuotient.lean#L19-L26

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sub_pow_eq_mul_sum_fin_48c4d365a9ba {n m : ℕ} (hm : m ≤ n) (s t : ℂ) :
    (s - t) * ∑ j : Fin n, (if (j : ℕ) < m then s ^ (m - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) = s ^ m - t ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«sub_pow_eq_mul_sum_fin» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sub_pow_eq_mul_sum_fin_48c4d365a9ba
