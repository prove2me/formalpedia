-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tangentGauss_indicator_eq_3ffb47ec0d7b
-- name    : P2M_GroundTheory_Heights__Heights_tangentGauss_indicator_eq_3ffb47ec0d7b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:07.58522+00:00
-- url     : https://prove2.me/theorems/e01252b2-ff9b-4e22-a979-f64d2b711b78
-- title:
--   P2 M Ground Theory Heights  Heights tangent Gauss indicator eq 3ffb47ec0d7b: P2 M Ground Theory Heights  Heights tangent Gauss indicator eq 3ffb47ec0d7b
-- statement:
--   The P2 M Ground Theory Heights  Heights tangent Gauss indicator eq 3ffb47ec0d7b construction uses the P2 M Ground Theory Heights  Heights tangent Gauss indicator eq 3ffb47ec0d7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment
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
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_tangentGauss_indicator_eq_3ffb47ec0d7b {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) =
      if |r| * ‖linProj π (firstCoordVec n)‖ < 1 then (1 : ℝ≥0∞) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tangentGauss_indicator_eq» := P2M_GroundTheory_Heights__Heights_tangentGauss_indicator_eq_3ffb47ec0d7b
