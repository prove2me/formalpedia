-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyMeasure_lintegral_min_one_sq_lt_top
-- name    : ProbabilityTheory.IsLevyMeasure.lintegral_min_one_sq_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:42:24.868351+00:00
-- url     : https://prove2.me/theorems/6fd9c469-173c-4538-a7c7-e16ba2aa87d1
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyMeasure.lintegral_min_one_sq_lt_top
-- statement:
--   The integral of `min(1, x²)` with respect to a Levy measure is finite. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyMeasure.lean#L66

import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Order.Basic

theorem ProbabilityTheory.IsLevyMeasure.lintegral_min_one_sq_lt_top : ∀ {ν : @MeasureTheory.Measure Real Real.measurableSpace},
  ProbabilityTheory.IsLevyMeasure ν →
    @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
      (@MeasureTheory.lintegral Real Real.measurableSpace ν fun x =>
        ENNReal.ofReal
          (@Min.min Real Real.instMin (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
            (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) x
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@Top.top ENNReal ENNReal.instTop) := by sorry
