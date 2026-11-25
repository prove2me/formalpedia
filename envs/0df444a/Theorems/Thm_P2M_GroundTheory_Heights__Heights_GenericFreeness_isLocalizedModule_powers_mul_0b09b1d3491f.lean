-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isLocalizedModule_powers_mul_0b09b1d3491f
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_isLocalizedModule_powers_mul_0b09b1d3491f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:33.386885+00:00
-- url     : https://prove2.me/theorems/378abeca-4112-47fc-9396-c8a30c872038
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness is Localized Module powers mul 0b09b1d3491f: P2 M Ground Theory Heights  Heights Generic Freeness is Localized Module powers mul 0b09b1d3491f
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness is Localized Module powers mul 0b09b1d3491f construction uses the P2 M Ground Theory Heights  Heights Generic Freeness is Localized Module powers mul 0b09b1d3491f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L46-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L46-L94

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

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_isLocalizedModule_powers_mul_0b09b1d3491f (a c : A) {M N P : Type*} [AddCommGroup M] [Module A M]
    {Ra : Type*} [CommRing Ra] [Algebra A Ra] [IsLocalization.Away a Ra]
    [AddCommGroup N] [Module A N] [Module Ra N] [IsScalarTower A Ra N]
    [AddCommGroup P] [Module A P] [Module Ra P] [IsScalarTower A Ra P]
    (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers a) g]
    (h : N →ₗ[Ra] P) [IsLocalizedModule (Submonoid.powers (algebraMap A Ra c)) h] :
    IsLocalizedModule (Submonoid.powers (a * c)) (h.restrictScalars A ∘ₗ g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«isLocalizedModule_powers_mul» := P2M_GroundTheory_Heights__Heights_GenericFreeness_isLocalizedModule_powers_mul_0b09b1d3491f
