-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_quotient_lift_injective_e78c2adbb3ac
-- name    : P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_quotient_lift_injective_e78c2adbb3ac
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:51.136543+00:00
-- url     : https://prove2.me/theorems/3c2b1afb-5917-485b-9675-8fd522256b8a
-- title:
--   P2 M Ground Theory Heights  Heights Generic Fibre Model Transport quotient lift injective e78c2adbb3ac: P2 M Ground Theory Heights  Heights Generic Fibre Model Transport quotient lift injective e78c2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Fibre Model Transport quotient lift injective e78c2adbb3ac construction uses the P2 M Ground Theory Heights  Heights Generic Fibre Model Transport quotient lift injective e78c2adbb3ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/QuotientLiftInjective.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/QuotientLiftInjective.lean#L44-L51

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

theorem P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_quotient_lift_injective_e78c2adbb3ac {A F : Type*} [CommRing A] [Field F] (φ : A →+* F) (P : Ideal A)
    (h : RingHom.ker φ = P) (hP : ∀ a ∈ P, φ a = 0) : Function.Injective (Ideal.Quotient.lift P φ hP) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFibreModelTransport».«quotient_lift_injective» := P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_quotient_lift_injective_e78c2adbb3ac
