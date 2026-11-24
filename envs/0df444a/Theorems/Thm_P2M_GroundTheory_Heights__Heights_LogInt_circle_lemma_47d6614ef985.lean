-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_circle_lemma_47d6614ef985
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_circle_lemma_47d6614ef985
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:19.970642+00:00
-- url     : https://prove2.me/theorems/3154db3c-f42f-4c77-8ef8-dcd469f7a9dd
-- title:
--   P2 M Ground Theory Heights  Heights Log Int circle lemma 47d6614ef985: P2 M Ground Theory Heights  Heights Log Int circle lemma 47d6614ef985
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int circle lemma 47d6614ef985 construction uses the P2 M Ground Theory Heights  Heights Log Int circle lemma 47d6614ef985 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntCircle.lean#L114-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntCircle.lean#L114-L200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt

theorem P2M_GroundTheory_Heights__Heights_LogInt_circle_lemma_47d6614ef985 {V : Type*} [MeasurableSpace V] (μ : Measure V) [SFinite μ]
    (S : Set V) (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤)
    (R : ℝ → V → V) (hR : Measurable (Function.uncurry R))
    (hpres : ∀ θ, MeasurePreserving (R θ) μ μ) (hinv : ∀ θ, R θ ⁻¹' S = S)
    (F : V → ℂ) (hF : Measurable F) (c : ℕ → V → ℂ) (D d0 : ℕ) (hd0 : d0 ≤ D)
    (hexp : ∀ θ u, F (R θ u) = ∑ d ∈ Finset.range (D + 1), c d u * circleMap 0 1 θ ^ d)
    (hint : IntegrableOn (fun u => Real.log ‖c d0 u‖) S μ)
    (hnz : ∀ᵐ u ∂(μ.restrict S), c d0 u ≠ 0)
    (M : ℝ) (hM : ∀ u ∈ S, ‖F u‖ ≤ M) :
    IntegrableOn (fun u => Real.log ‖F u‖) S μ ∧ ∀ᵐ u ∂(μ.restrict S), F u ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«circle_lemma» := P2M_GroundTheory_Heights__Heights_LogInt_circle_lemma_47d6614ef985
