-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_id_poissonMeasure
-- name    : ProbabilityTheory.integral_id_poissonMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:14:03.672974+00:00
-- url     : https://prove2.me/theorems/6c9d7a76-f448-4df6-908d-ee86df1032e0
-- title:
--   LeanLevy: ProbabilityTheory.integral_id_poissonMeasure
-- statement:
--   **Mean of the Poisson distribution (integral form):** Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4//home/willr/projects/Prove2Me/scratch/leanlevy_bulk_20261027/source/LeanLevy/Probability/Poisson.lean#L160

import Definitions.Def_LeanLevy_Probability_Poisson
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_LeanLevy_Probability_Characteristic

theorem ProbabilityTheory.integral_id_poissonMeasure : ∀ (r : NNReal),
  @Eq Real
    (@MeasureTheory.integral Nat Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      Nat.instMeasurableSpace (ProbabilityTheory.poissonMeasure r) fun n => @Nat.cast Real Real.instNatCast n)
    ↑r := by sorry
