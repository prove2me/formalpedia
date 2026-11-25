-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_mem_smul_top_of_mem_42c739f56100
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_mem_smul_top_of_mem_42c739f56100
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:52.097711+00:00
-- url     : https://prove2.me/theorems/f2518cd7-cd20-43e1-a9b0-ea34f57f86cc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets smul mem smul top of mem 42c739f56100: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets s
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets smul mem smul top of mem 42c739f56100 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets smul mem smul top of mem 42c739f56100 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularElement.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularElement.lean#L71-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularElement
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
open IsLocalRing TensorProduct
open scoped Pointwise
variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_mem_smul_top_of_mem_42c739f56100 (I : Ideal A) (y : B) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : y • x ∈ I • (⊤ : Submodule A M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«smul_mem_smul_top_of_mem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_mem_smul_top_of_mem_42c739f56100
