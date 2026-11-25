-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_polydisc_cons_mem_ball
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.polydisc_cons_mem_ball
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:22.767309+00:00
-- url     : https://prove2.me/theorems/367a738e-8e38-53b3-b0a1-302ecf861c31
-- title:
--   Geometry Of Numbers Theory: polydisc cons mem ball
-- statement:
--   The Geometry Of Numbers Theory construction uses the polydisc cons mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/PolydiscSt.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/PolydiscSt.lean#L7-L13

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.polydisc_cons_mem_ball {D : ℕ} {R : ℝ} (hR : 0 < R) {x : ℂ} {y : Fin D → ℂ}
    (hx : ‖x‖ < R) (hy : ‖y‖ < R) : (Fin.cons x y : Fin (D + 1) → ℂ) ∈ Metric.ball 0 R := by sorry
