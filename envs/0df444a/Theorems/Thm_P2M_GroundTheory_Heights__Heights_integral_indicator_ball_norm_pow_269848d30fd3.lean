-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_indicator_ball_norm_pow_269848d30fd3
-- name    : P2M_GroundTheory_Heights__Heights_integral_indicator_ball_norm_pow_269848d30fd3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:58.113134+00:00
-- url     : https://prove2.me/theorems/bdb6f0b5-96da-43c0-812c-d78b7fcd50ce
-- title:
--   P2 M Ground Theory Heights  Heights integral indicator ball norm pow 269848d30fd3: P2 M Ground Theory Heights  Heights integral indicator ball norm pow 269848d30fd3
-- statement:
--   The P2 M Ground Theory Heights  Heights integral indicator ball norm pow 269848d30fd3 construction uses the P2 M Ground Theory Heights  Heights integral indicator ball norm pow 269848d30fd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeChartArea.lean#L12-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeChartArea.lean#L12-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)

theorem P2M_GroundTheory_Heights__Heights_integral_indicator_ball_norm_pow_269848d30fd3 (e : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t : ℂ, (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) t =
      Real.pi * R ^ (2 * (e + 1)) / (e + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«integral_indicator_ball_norm_pow» := P2M_GroundTheory_Heights__Heights_integral_indicator_ball_norm_pow_269848d30fd3
