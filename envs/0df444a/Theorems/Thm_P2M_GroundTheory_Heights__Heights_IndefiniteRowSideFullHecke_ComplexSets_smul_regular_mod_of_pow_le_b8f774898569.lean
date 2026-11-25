-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_regular_mod_of_pow_le_b8f774898569
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_regular_mod_of_pow_le_b8f774898569
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:44.910213+00:00
-- url     : https://prove2.me/theorems/ac7c8454-4b70-46e8-b278-0dac470733a4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets smul regular mod of pow le b8f774898569: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets smul regular mod of pow le b8f774898569 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets smul regular mod of pow le b8f774898569 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularElement.lean#L78-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularElement.lean#L78-L122

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
variable [IsNoetherianRing A] [IsLocalRing A] [Module.Flat A M]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_regular_mod_of_pow_le_b8f774898569 (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (J : Ideal A) :
    (∃ n, maximalIdeal A ^ n ≤ J) →
      ∀ z : M, y • z ∈ J • (⊤ : Submodule A M) → z ∈ J • (⊤ : Submodule A M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«smul_regular_mod_of_pow_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_regular_mod_of_pow_le_b8f774898569
