-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_derivation_det_not_mem_28a934ea20c0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_derivation_det_not_mem_28a934ea20c0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:32.839577+00:00
-- url     : https://prove2.me/theorems/851ae396-9e8d-4a51-b4cd-3257d1a1434f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem of derivation det not mem 28a934ea20c0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem of derivation det not mem 28a934ea20c0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem of derivation det not mem 28a934ea20c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDerivationCotangentIndependent.lean#L17-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDerivationCotangentIndependent.lean#L17-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationCotangentIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDerivationCotangentIndependent
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
open IsLocalRing Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_derivation_det_not_mem_28a934ea20c0 {T : Type} [CommRing T] (P : Ideal T) [P.IsPrime] {h : ℕ}
    (D : Fin h → Derivation ℤ T T) (f : Fin h → T) (hf : ∀ i, f i ∈ P)
    (hdet : (Matrix.of fun i j => D j (f i)).det ∉ P) (b : Fin h → T) (t : T) (ht : t ∉ P)
    (hsum : t * ∑ i, b i * f i ∈ P ^ 2) (i : Fin h) : b i ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«mem_of_derivation_det_not_mem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_derivation_det_not_mem_28a934ea20c0
