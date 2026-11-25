-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_subfield_equiv_630b94a1146f
-- name    : P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_subfield_equiv_630b94a1146f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:53.5668+00:00
-- url     : https://prove2.me/theorems/c7790c9e-41a3-440c-8fb2-6c5ae48256b5
-- title:
--   P2 M Ground Theory Heights  Heights Generic Fibre Model Transport subfield equiv 630b94a1146f: P2 M Ground Theory Heights  Heights Generic Fibre Model Transport subfield equiv 630b94a1146f
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Fibre Model Transport subfield equiv 630b94a1146f construction uses the P2 M Ground Theory Heights  Heights Generic Fibre Model Transport subfield equiv 630b94a1146f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/QuotientLiftInjective.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/QuotientLiftInjective.lean#L53-L63

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

theorem P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_subfield_equiv_630b94a1146f {L A Φ : Type*} [Field L] [Field A] [Field Φ] (k : Subfield L) (α : L →+* A)
    (ι : Φ →+* A) (hr : ι.fieldRange = k.map α) : ∃ e : k ≃+* Φ, ∀ c, ι (e c) = α c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFibreModelTransport».«subfield_equiv» := P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_subfield_equiv_630b94a1146f
