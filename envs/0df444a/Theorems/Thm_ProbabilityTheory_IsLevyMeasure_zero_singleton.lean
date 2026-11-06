-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyMeasure_zero_singleton
-- name    : ProbabilityTheory.IsLevyMeasure.zero_singleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:42:49.223995+00:00
-- url     : https://prove2.me/theorems/2c354f47-075b-431e-b949-c84f174fe7d2
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyMeasure.zero_singleton
-- statement:
--   A Levy measure assigns zero mass to the origin. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyMeasure.lean#L62

import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Order.Basic

theorem ProbabilityTheory.IsLevyMeasure.zero_singleton : ∀ {ν : @MeasureTheory.Measure Real Real.measurableSpace},
  ProbabilityTheory.IsLevyMeasure ν →
    @Eq ENNReal
      (@DFunLike.coe (@MeasureTheory.Measure Real Real.measurableSpace) (Set Real) (fun x => ENNReal)
        (@MeasureTheory.Measure.instFunLike Real Real.measurableSpace) ν
        (@Singleton.singleton Real (Set Real) (@Set.instSingletonSet Real)
          (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))))
      (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) := by sorry
