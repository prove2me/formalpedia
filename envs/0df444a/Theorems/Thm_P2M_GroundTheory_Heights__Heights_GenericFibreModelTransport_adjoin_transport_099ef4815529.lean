-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_adjoin_transport_099ef4815529
-- name    : P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_adjoin_transport_099ef4815529
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:48.564284+00:00
-- url     : https://prove2.me/theorems/fd6bee72-8f15-491f-a1a0-c8363a297378
-- title:
--   P2 M Ground Theory Heights  Heights Generic Fibre Model Transport adjoin transport 099ef4815529: P2 M Ground Theory Heights  Heights Generic Fibre Model Transport adjoin transport 099ef4815529
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Fibre Model Transport adjoin transport 099ef4815529 construction uses the P2 M Ground Theory Heights  Heights Generic Fibre Model Transport adjoin transport 099ef4815529 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/QuotientLiftInjective.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/QuotientLiftInjective.lean#L10-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_QuotientLiftInjective
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
open GroundTheory.Heights₂.Heights.GenericFibreModelTransport
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_adjoin_transport_099ef4815529 {k₁ A₁ k₂ A₂ : Type*} [Field k₁] [Field A₁] [Algebra k₁ A₁] [Field k₂] [Field A₂]
    [Algebra k₂ A₂] (i : k₁ ≃+* k₂) (h : A₁ →+* A₂)
    (hc : (algebraMap k₂ A₂).comp i.toRingHom = h.comp (algebraMap k₁ A₁)) (s : Set A₁) (a : A₁) :
    Module.finrank k₁ (Algebra.adjoin k₁ s) = Module.finrank k₂ (Algebra.adjoin k₂ (h '' s)) ∧
      (Transcendental (Algebra.adjoin k₁ s) a ↔ Transcendental (Algebra.adjoin k₂ (h '' s)) (h a)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFibreModelTransport».«adjoin_transport» := P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_adjoin_transport_099ef4815529
