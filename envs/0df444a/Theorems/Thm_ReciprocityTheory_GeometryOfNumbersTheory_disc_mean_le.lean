-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_disc_mean_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.disc_mean_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:10.102566+00:00
-- url     : https://prove2.me/theorems/9fe7879a-74d1-444b-882f-45dcc05de991
-- title:
--   Geometry Of Numbers Theory: disc mean le
-- statement:
--   The Geometry Of Numbers Theory construction uses the disc mean le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L145-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L145-L177

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set

theorem ReciprocityTheory.GeometryOfNumbersTheory.disc_mean_le {R r : ℝ} (hr : 0 < r) (hrR : r < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) (w : ℝ → ℝ) (hwc : Continuous w)
    (hw : ∀ s, 0 ≤ w s) :
    ‖g 0‖ ^ 2 * ∫ z in Metric.ball (0 : ℂ) r, w ‖z‖ ≤
      ∫ z in Metric.ball (0 : ℂ) r, ‖g z‖ ^ 2 * w ‖z‖ := by sorry
