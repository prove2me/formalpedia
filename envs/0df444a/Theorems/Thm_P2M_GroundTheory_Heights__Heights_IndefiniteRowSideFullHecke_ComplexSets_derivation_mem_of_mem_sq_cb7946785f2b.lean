-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_derivation_mem_of_mem_sq_cb7946785f2b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_derivation_mem_of_mem_sq_cb7946785f2b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:54.517492+00:00
-- url     : https://prove2.me/theorems/229485aa-e7a6-4138-b986-0b9ea4b76b21
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets derivation mem of mem sq cb7946785f2b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets d
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets derivation mem of mem sq cb7946785f2b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets derivation mem of mem sq cb7946785f2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDerivationCotangentIndependent.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDerivationCotangentIndependent.lean#L9-L15

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_derivation_mem_of_mem_sq_cb7946785f2b {T : Type} [CommRing T] (P : Ideal T) (D : Derivation ℤ T T)
    {x : T} (hx : x ∈ P ^ 2) : D x ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«derivation_mem_of_mem_sq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_derivation_mem_of_mem_sq_cb7946785f2b
