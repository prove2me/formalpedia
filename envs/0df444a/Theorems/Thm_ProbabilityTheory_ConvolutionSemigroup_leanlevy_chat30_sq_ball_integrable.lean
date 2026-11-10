-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat30_sq_ball_integrable
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_sq_ball_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:24:33.880233+00:00
-- url     : https://prove2.me/theorems/6322e219-a8a3-40d4-9175-ea893cccf673
-- title:
--   Integrability of squared Lévy jump sizes inside a finite radius
-- statement:
--   A Lévy measure has integrable squared marks on every finite-radius interval, including radii above one; this source-backed lemma is necessary for the first quadratic identity in ν-side Lévy–Khintchine algebra.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4765

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Complex Filter Topology
open ProbabilityTheory.ConvolutionSemigroup
open scoped NNReal ENNReal ComplexOrder

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_sq_ball_integrable
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (r : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} ν := by sorry
