-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_linearEquiv_fa7014fc8534
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_linearEquiv_fa7014fc8534
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:21.98223+00:00
-- url     : https://prove2.me/theorems/027e21c6-e9b8-4762-9611-7ebbe33c7592
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of linear Equiv fa7014fc8534: P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of linear Equiv fa7014fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of linear Equiv fa7014fc8534 construction uses the P2 M Ground Theory Heights  Heights Generic Freeness Is Generically Free of linear Equiv fa7014fc8534 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L112-L117

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

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_linearEquiv_fa7014fc8534 {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (e : M ≃ₗ[A] M') (hM : IsGenericallyFree A M) : IsGenericallyFree A M' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«IsGenericallyFree».«of_linearEquiv» := P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_linearEquiv_fa7014fc8534
