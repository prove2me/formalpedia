-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_polydisc_mean_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.polydisc_mean_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:58.379608+00:00
-- url     : https://prove2.me/theorems/201898ed-9965-48d8-a18e-06746d3a4d76
-- title:
--   Geometry Of Numbers Theory: polydisc mean le
-- statement:
--   The Geometry Of Numbers Theory construction uses the polydisc mean le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/PolydiscSt.lean#L24-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/PolydiscSt.lean#L24-L116

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory

theorem ReciprocityTheory.GeometryOfNumbersTheory.polydisc_mean_le {D : ℕ} {R r : ℝ} (hr : 0 < r) (hrR : r < R) (f : (Fin D → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (w : Fin D → ℝ → ℝ)
    (hwc : ∀ j, Continuous (w j)) (hw : ∀ j s, 0 ≤ w j s) :
    ‖f 0‖ ^ 2 * ∏ j, ∫ z in Metric.ball (0 : ℂ) r, w j ‖z‖ ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) r, ‖f z‖ ^ 2 * ∏ j, w j ‖z j‖ := by sorry
