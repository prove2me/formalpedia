-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneFibreAverage_of_lt_6291d9b63762
-- name    : P2M_GroundTheory_Heights__Heights_coneFibreAverage_of_lt_6291d9b63762
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:22.904699+00:00
-- url     : https://prove2.me/theorems/145d0186-1965-4b0c-80f8-8e1857642111
-- title:
--   P2 M Ground Theory Heights  Heights cone Fibre Average of lt 6291d9b63762: P2 M Ground Theory Heights  Heights cone Fibre Average of lt 6291d9b63762
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Fibre Average of lt 6291d9b63762 construction uses the P2 M Ground Theory Heights  Heights cone Fibre Average of lt 6291d9b63762 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreAverage.lean#L21-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreAverage.lean#L21-L37

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

theorem P2M_GroundTheory_Heights__Heights_coneFibreAverage_of_lt_6291d9b63762 {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      1 * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneFibreAverage_of_lt» := P2M_GroundTheory_Heights__Heights_coneFibreAverage_of_lt_6291d9b63762
