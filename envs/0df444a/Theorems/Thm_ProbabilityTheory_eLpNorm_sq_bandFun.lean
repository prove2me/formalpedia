-- Prove2me | Theorems.Thm_ProbabilityTheory_eLpNorm_sq_bandFun
-- name    : ProbabilityTheory.eLpNorm_sq_bandFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:28:15.407913+00:00
-- url     : https://prove2.me/theorems/a71fd861-f63d-4201-8ad6-3131d952d2cd
-- title:
--   LeanLevy: ProbabilityTheory.eLpNorm_sq_bandFun
-- statement:
--   The squared `L²` seminorm of a band indicator over a measurable mark set `C`. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L1337

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.eLpNorm_sq_bandFun :
  ∀ {ν : MeasureTheory.Measure ℝ} [MeasureTheory.SigmaFinite ν] {C : Set ℝ},
  MeasurableSet C →
    ∀ (s t : ℝ),
      MeasureTheory.eLpNorm ((Set.Ioc s t ×ˢ C).indicator fun p => p.2) 2 (MeasureTheory.volume.prod ν) ^ 2 =
        ENNReal.ofReal (t - s) * ∫⁻ (x : ℝ) in C, ENNReal.ofReal (x ^ 2) ∂ν := by sorry
