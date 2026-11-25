-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_mk_bea9a232f8f0
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_mk_bea9a232f8f0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:53.305074+00:00
-- url     : https://prove2.me/theorems/16e46759-2f2d-5bf6-ad1a-2848a85f981f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num quot Equiv mk bea9a232f8f0: P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num quot Equiv mk bea9a232f8f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num quot Equiv mk bea9a232f8f0 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num quot Equiv mk bea9a232f8f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConjIntNum.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConjIntNum.lean#L28-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_mk_bea9a232f8f0 (τ : F ≃+* F) (J : Ideal (MRing ι F)) (f : MRing ι F) :
    quotEquiv τ J (Ideal.Quotient.mk J f) = Ideal.Quotient.mk _ (MvPolynomial.map (τ : F →+* F) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConjIntNum».«quotEquiv_mk» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_mk_bea9a232f8f0
