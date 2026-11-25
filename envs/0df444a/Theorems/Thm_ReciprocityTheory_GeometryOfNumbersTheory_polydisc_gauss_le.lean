-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_polydisc_gauss_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.polydisc_gauss_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:46.464799+00:00
-- url     : https://prove2.me/theorems/1d051db4-d986-42ef-a8f0-9a58153fb05b
-- title:
--   Geometry Of Numbers Theory: polydisc gauss le
-- statement:
--   The Geometry Of Numbers Theory construction uses the polydisc gauss le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/PolydiscSt.lean#L118-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/PolydiscSt.lean#L118-L131

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.polydisc_gauss_le {D : ℕ} {R r : ℝ} (hr : 0 < r) (hrR : r < R) (f : (Fin D → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (a : Fin D → ℝ) :
    ‖f 0‖ ^ 2 * ∏ j, discI (a j) r ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) r, ‖f z‖ ^ 2 * Real.exp (-∑ j, a j * ‖z j‖ ^ 2) := by sorry
