-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_algebraicIndependent_linComb_4848053020e4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_algebraicIndependent_linComb_4848053020e4
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:50.988838+00:00
-- url     : https://prove2.me/theorems/00f354c7-295d-4ff2-ba1f-3b0401e8ba50
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge algebraic Independent lin Comb 4848053020e4: P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge algebraic Indepen
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge algebraic Independent lin Comb 4848053020e4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Span Bundle Trdeg Ge algebraic Independent lin Comb 4848053020e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpanBundleTrdegGe.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpanBundleTrdegGe.lean#L11-L36

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_algebraicIndependent_linComb_4848053020e4 {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    {i : ℕ} (s : Fin i → Φ) (hs : AlgebraicIndependent Ω s) (A : Matrix (Fin i) (Fin i) Ω)
    (hA : IsUnit A) : AlgebraicIndependent Ω (fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SpanBundleTrdegGe».«algebraicIndependent_linComb» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_algebraicIndependent_linComb_4848053020e4
