-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_integrableOn_ball_levy
-- name    : ProbabilityTheory.leanlevy_chat32_remainder_integrableOn_ball_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:49:31.48457+00:00
-- url     : https://prove2.me/theorems/046eafcf-ec47-4a03-a37d-9bd5d8a2379a
-- title:
--   Lévy-measure cubic remainder integrability
-- statement:
--   Lévy-measure cubic remainder integrability
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3886-L3910

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_remainder_integrableOn_ball_levy {r : ℝ} (hr1 : r ≤ 1) (ξ : ℝ) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} ν := by sorry
