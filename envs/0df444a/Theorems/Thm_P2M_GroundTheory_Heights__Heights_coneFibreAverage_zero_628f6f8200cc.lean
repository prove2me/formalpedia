-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneFibreAverage_zero_628f6f8200cc
-- name    : P2M_GroundTheory_Heights__Heights_coneFibreAverage_zero_628f6f8200cc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:59.47733+00:00
-- url     : https://prove2.me/theorems/e3fe1a2f-2e3f-47e3-9296-840560b4cbc8
-- title:
--   P2 M Ground Theory Heights  Heights cone Fibre Average zero 628f6f8200cc: P2 M Ground Theory Heights  Heights cone Fibre Average zero 628f6f8200cc
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Fibre Average zero 628f6f8200cc construction uses the P2 M Ground Theory Heights  Heights cone Fibre Average zero 628f6f8200cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreAverage.lean#L39-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreAverage.lean#L39-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreAverage
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_coneFibreAverage_zero_628f6f8200cc {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J)
    (hfib : ∀ᵐ π : Fin 0 → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 0), fibreCount h J π w ≠ ⊤) :
    ∫⁻ π : Fin 0 → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1, (fibreCount h J π w : ℝ≥0∞) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1) *
        Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneFibreAverage_zero» := P2M_GroundTheory_Heights__Heights_coneFibreAverage_zero_628f6f8200cc
