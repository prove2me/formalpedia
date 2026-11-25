-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_integral_ball_polar
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.pgds_integral_ball_polar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:08.417801+00:00
-- url     : https://prove2.me/theorems/0b347acd-2000-41a5-b4b1-a259a89e41f3
-- title:
--   Geometry Of Numbers Theory: pgds integral ball polar
-- statement:
--   The Geometry Of Numbers Theory construction uses the pgds integral ball polar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L17-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L17-L56

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.pgds_integral_ball_polar {r : ℝ} (F : ℂ → ℝ) (hF : ContinuousOn F (Metric.closedBall 0 r)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
        (Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi) ∧
    ∫ z in Metric.ball (0 : ℂ) r, F z =
      ∫ s in Ioo 0 r, ∫ θ in Ioo (-Real.pi) Real.pi, s * F (Complex.polarCoord.symm (s, θ)) := by sorry
