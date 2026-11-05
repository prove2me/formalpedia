-- Prove2me | Theorems.Thm_ProbabilityTheory_poissonFactorialMoment2_hasSum
-- name    : ProbabilityTheory.poissonFactorialMoment2_hasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:29:20.859722+00:00
-- url     : https://prove2.me/theorems/94e6204e-95a0-4cfe-9189-7e50ffad3a3e
-- title:
--   Second factorial moment of a Poisson law (LeanLevy source)
-- statement:
--   The second factorial moment E[N(N-1)] of a Poisson count N with rate r equals r squared. This exact original LeanLevy theorem supplies a source-certified ingredient for the Poisson variance and compensated-jump L2 isometry proofs.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/Probability/Poisson.lean, original theorem and private factorial moment shift at lines 82–106.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

theorem ProbabilityTheory.poissonFactorialMoment2_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ((↑n : ℝ) * (↑n - 1)) *
      (poissonMeasure r).real {n}) ((r : ℝ) ^ 2) := by sorry
