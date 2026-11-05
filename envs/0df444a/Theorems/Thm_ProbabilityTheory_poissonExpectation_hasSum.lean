-- Prove2me | Theorems.Thm_ProbabilityTheory_poissonExpectation_hasSum
-- name    : ProbabilityTheory.poissonExpectation_hasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:19:00.375353+00:00
-- url     : https://prove2.me/theorems/20a90fde-bc97-4708-9284-f4a9c916889a
-- title:
--   Poisson expectation equals its rate (LeanLevy source)
-- statement:
--   The expected count under a Poisson law with rate r is r, expressed as a convergent real series. This is the original LeanLevy Poisson expectation theorem needed for Campbell's formula.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/Probability/Poisson.lean, source exact theorem at line 74 and supporting private shift lemma.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

theorem ProbabilityTheory.poissonExpectation_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ↑n * (poissonMeasure r).real {n}) (r : ℝ) := by sorry
