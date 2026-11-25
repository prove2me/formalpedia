-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hausdorffMeasure_coneSet_ball_le_b81ecaae35f7
-- name    : P2M_GroundTheory_Heights__Heights_hausdorffMeasure_coneSet_ball_le_b81ecaae35f7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:15.499018+00:00
-- url     : https://prove2.me/theorems/1dbf1e34-1e16-4178-aee3-822141112770
-- title:
--   P2 M Ground Theory Heights  Heights hausdorff Measure cone Set ball le b81ecaae35f7: P2 M Ground Theory Heights  Heights hausdorff Measure cone Set ball le b81ecaae35f7
-- statement:
--   The P2 M Ground Theory Heights  Heights hausdorff Measure cone Set ball le b81ecaae35f7 construction uses the P2 M Ground Theory Heights  Heights hausdorff Measure cone Set ball le b81ecaae35f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalMass.lean#L38-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalMass.lean#L38-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
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
open MvPolynomial MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_hausdorffMeasure_coneSet_ball_le_b81ecaae35f7 (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (R : ℝ) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J ∩ Metric.ball 0 R) ≤
      ((‖(h.pointOfL.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖₊ : ℝ≥0∞) ^
          ((2 * d : ℕ) : ℝ)) *
        Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J ∩
          Metric.ball 0 (‖(h.pointOfL : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hausdorffMeasure_coneSet_ball_le» := P2M_GroundTheory_Heights__Heights_hausdorffMeasure_coneSet_ball_le_b81ecaae35f7
