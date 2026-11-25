-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_free_965944990c29
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_free_965944990c29
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:22.342951+00:00
-- url     : https://prove2.me/theorems/d7353104-28d8-4499-813f-3cbe277b7b18
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of free 965944990c29: P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of free 965944990c29
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of free 965944990c29 construction uses the P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of free 965944990c29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L130-L133

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

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_free_965944990c29 [Nontrivial A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M] :
    IsGenericallyFree A M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«isGenericallyFree_of_free» := P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_free_965944990c29
