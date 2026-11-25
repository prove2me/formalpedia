-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_injective_29d662892878
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_injective_29d662892878
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:46.52298+00:00
-- url     : https://prove2.me/theorems/5c8baa5d-da03-4f7b-b4ce-7d44e15c0cb1
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of injective 29d662892878: P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of injective 29d662892878
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of injective 29d662892878 construction uses the P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of injective 29d662892878 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L135-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L135-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
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
open GroundTheory.Heights₂.Heights.GenericFreeness
open Module
universe u
variable {A : Type u} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_injective_29d662892878 [IsDomain A] {N M : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M]
    [Module A M] (i : N →ₗ[A] M) (hi : Function.Injective i) (a : A) (ha : a ≠ 0)
    (hsat : ∀ m : M, ∃ k : ℕ, a ^ k • m ∈ LinearMap.range i) (hN : IsGenericallyFree A N) :
    IsGenericallyFree A M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«IsGenericallyFree».«of_injective» := P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_injective_29d662892878
