-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sum_fin_ite_lt_6a0fe4d5d9a1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sum_fin_ite_lt_6a0fe4d5d9a1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:04.624895+00:00
-- url     : https://prove2.me/theorems/e11e0b7c-86ef-4539-8894-005d53eaafae
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sum fin ite lt 6a0fe4d5d9a1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sum fin ite
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sum fin ite lt 6a0fe4d5d9a1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sum fin ite lt 6a0fe4d5d9a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonicDifferenceQuotient.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonicDifferenceQuotient.lean#L11-L17

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sum_fin_ite_lt_6a0fe4d5d9a1 {n m : ℕ} (hm : m ≤ n) (f : ℕ → ℂ) :
    ∑ j : Fin n, (if (j : ℕ) < m then f j else 0) = ∑ j ∈ range m, f j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«sum_fin_ite_lt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sum_fin_ite_lt_6a0fe4d5d9a1
