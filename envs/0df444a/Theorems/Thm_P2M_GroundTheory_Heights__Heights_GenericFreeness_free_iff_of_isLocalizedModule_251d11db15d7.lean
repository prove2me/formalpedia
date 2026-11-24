-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_free_iff_of_isLocalizedModule_251d11db15d7
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_free_iff_of_isLocalizedModule_251d11db15d7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:27.687803+00:00
-- url     : https://prove2.me/theorems/936eb298-64b0-4f75-965f-3e62f39dc759
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness free iff of is Localized Module 251d11db15d7: P2 M Ground Theory Heights  Heights Generic Freeness free iff of is Localized Module 251d11db15d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness free iff of is Localized Module 251d11db15d7 construction uses the P2 M Ground Theory Heights  Heights Generic Freeness free iff of is Localized Module 251d11db15d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L17-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L17-L44

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

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_free_iff_of_isLocalizedModule_251d11db15d7 (f : A) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers f) g]
    (Rf : Type*) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf] [Module Rf N]
    [IsScalarTower A Rf N] :
    Module.Free Rf N ↔ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«free_iff_of_isLocalizedModule» := P2M_GroundTheory_Heights__Heights_GenericFreeness_free_iff_of_isLocalizedModule_251d11db15d7
