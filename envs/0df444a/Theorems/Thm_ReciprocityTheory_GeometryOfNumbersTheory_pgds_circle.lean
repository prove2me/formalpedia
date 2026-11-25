-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_circle
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.pgds_circle
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:42.859977+00:00
-- url     : https://prove2.me/theorems/a2eac605-3966-578e-90dd-2812361cad97
-- title:
--   Geometry Of Numbers Theory: pgds circle
-- statement:
--   The Geometry Of Numbers Theory construction uses the pgds circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L116-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L116-L143

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.pgds_circle {R s : ℝ} (hs : 0 < s) (hsR : s < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) :
    2 * Real.pi * ‖g 0‖ ^ 2 ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := by sorry
