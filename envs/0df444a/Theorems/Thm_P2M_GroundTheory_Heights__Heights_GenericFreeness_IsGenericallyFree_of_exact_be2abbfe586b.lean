-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_exact_be2abbfe586b
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_exact_be2abbfe586b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:52.803588+00:00
-- url     : https://prove2.me/theorems/fdd52cf7-c44a-424c-8365-af0fd07fa61b
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of exact be2abbfe586b: P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of exact be2abbfe586b
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of exact be2abbfe586b construction uses the P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of exact be2abbfe586b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L163-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L163-L183

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

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_exact_be2abbfe586b [IsDomain A] {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] (i : N₁ →ₗ[A] N₂) (p : N₂ →ₗ[A] N₃)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (h₁ : IsGenericallyFree A N₁) (h₃ : IsGenericallyFree A N₃) : IsGenericallyFree A N₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«IsGenericallyFree».«of_exact» := P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_exact_be2abbfe586b
