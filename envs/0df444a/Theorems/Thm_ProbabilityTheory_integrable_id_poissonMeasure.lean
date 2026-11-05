-- Prove2me | Theorems.Thm_ProbabilityTheory_integrable_id_poissonMeasure
-- name    : ProbabilityTheory.integrable_id_poissonMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:13:37.727836+00:00
-- url     : https://prove2.me/theorems/b5167bf4-0def-453d-b207-b6d2d96524c7
-- title:
--   LeanLevy: ProbabilityTheory.integrable_id_poissonMeasure
-- statement:
--   **Integrability of the identity against a Poisson law:** `n ↦ n` is integrable against Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4//home/willr/projects/Prove2Me/scratch/leanlevy_bulk_20261027/source/LeanLevy/Probability/Poisson.lean#L152

import Definitions.Def_LeanLevy_Probability_Poisson
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_LeanLevy_Probability_Characteristic

theorem ProbabilityTheory.integrable_id_poissonMeasure : ∀ (r : NNReal),
  @MeasureTheory.Integrable Real
    (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
    (@SeminormedAddGroup.toContinuousENorm Real
      (@SeminormedAddCommGroup.toSeminormedAddGroup Real
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Real
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Real
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Real
              (@NormedCommRing.toSeminormedCommRing Real Real.normedCommRing))))))
    Nat Nat.instMeasurableSpace (fun n => @Nat.cast Real Real.instNatCast n) (ProbabilityTheory.poissonMeasure r) := by sorry
