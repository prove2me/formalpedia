-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_exists_injective_cone_3ee5f0062363
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_exists_injective_cone_3ee5f0062363
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:46.866317+00:00
-- url     : https://prove2.me/theorems/1832a082-735f-42b1-8d83-7919616e7a63
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge exists injective cone 3ee5f0062363: P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge exists injective cone 3ee5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge exists injective cone 3ee5f0062363 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge exists injective cone 3ee5f0062363 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpanBundleTrdegGe.lean#L60-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpanBundleTrdegGe.lean#L60-L93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpanBundleTrdegGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_exists_injective_cone_3ee5f0062363 {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    (K : Type*) {i : ℕ} (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    ∃ Ψ : MvPolynomial (Fin i) (MvPolynomial K Ω) →+* MvPolynomial (Option K) Φ, Function.Injective Ψ ∧
      (∀ p, Ψ (C p) = rename some (map (algebraMap Ω Φ) p)) ∧ ∀ r, Ψ (X r) = C (σ r) * X none := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SpanBundleTrdegGe».«exists_injective_cone» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_exists_injective_cone_3ee5f0062363
