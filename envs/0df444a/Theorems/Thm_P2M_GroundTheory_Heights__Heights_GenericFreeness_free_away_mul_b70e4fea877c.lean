-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_free_away_mul_b70e4fea877c
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_free_away_mul_b70e4fea877c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:24.395254+00:00
-- url     : https://prove2.me/theorems/629be841-cb07-4a50-930c-356cd2e668ac
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness free away mul b70e4fea877c: P2 M Ground Theory Heights  Heights Generic Freeness free away mul b70e4fea877c
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness free away mul b70e4fea877c construction uses the P2 M Ground Theory Heights  Heights Generic Freeness free away mul b70e4fea877c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L96-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L96-L110

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

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_free_away_mul_b70e4fea877c {f : A} (g : A) {M : Type*} [AddCommGroup M] [Module A M]
    (hf : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free (Localization.Away (f * g)) (LocalizedModule (Submonoid.powers (f * g)) M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«free_away_mul» := P2M_GroundTheory_Heights__Heights_GenericFreeness_free_away_mul_b70e4fea877c
