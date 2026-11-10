-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_sq_integrableOn_ball_levy
-- name    : ProbabilityTheory.leanlevy_chat32_sq_integrableOn_ball_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:49:33.816982+00:00
-- url     : https://prove2.me/theorems/387ed09f-a219-4359-a2c9-8682282fc8b3
-- title:
--   Lévy-measure square integrability on a ball
-- statement:
--   Lévy-measure square integrability on a ball
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3847-L3885

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_sq_integrableOn_ball_levy {ν : Measure ℝ} (hν : IsLevyMeasure ν) (r : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} ν := by sorry
