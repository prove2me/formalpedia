-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_injective_aeval_mul_X_80cf88eaa3b4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_injective_aeval_mul_X_80cf88eaa3b4
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:44.550324+00:00
-- url     : https://prove2.me/theorems/ca5a2e99-1a93-40a6-9dae-f0756d55b039
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge injective aeval mul X 80cf88eaa3b4: P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge injective aeval mul X 80cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge injective aeval mul X 80cf88eaa3b4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge injective aeval mul X 80cf88eaa3b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpanBundleTrdegGe.lean#L38-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpanBundleTrdegGe.lean#L38-L58

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_injective_aeval_mul_X_80cf88eaa3b4 {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ] {i : ℕ}
    (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    Function.Injective (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SpanBundleTrdegGe».«injective_aeval_mul_X» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_injective_aeval_mul_X_80cf88eaa3b4
