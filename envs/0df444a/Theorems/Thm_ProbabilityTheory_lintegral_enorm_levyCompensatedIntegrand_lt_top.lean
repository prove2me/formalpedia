-- Prove2me | Theorems.Thm_ProbabilityTheory_lintegral_enorm_levyCompensatedIntegrand_lt_top
-- name    : ProbabilityTheory.lintegral_enorm_levyCompensatedIntegrand_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:23:03.197992+00:00
-- url     : https://prove2.me/theorems/6ece9a29-b154-4ee1-be35-575f93ef11bc
-- title:
--   LeanLevy: ProbabilityTheory.lintegral_enorm_levyCompensatedIntegrand_lt_top
-- statement:
--   The Lebesgue integral of `‖levyCompensatedIntegrand ξ ·‖ₑ` against a Lévy measure is finite. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CompensatedIntegral.lean#L144

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

theorem ProbabilityTheory.lintegral_enorm_levyCompensatedIntegrand_lt_top : ∀ {ν : @MeasureTheory.Measure Real Real.measurableSpace},
  ProbabilityTheory.IsLevyMeasure ν →
    ∀ (ξ : Real),
      @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
        (@MeasureTheory.lintegral Real Real.measurableSpace ν fun x =>
          @ENorm.enorm Complex
            (@ContinuousENorm.toENorm Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedAddGroup.toPseudoMetricSpace Complex
                    (@SeminormedAddCommGroup.toSeminormedAddGroup Complex
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                            (@NormedCommRing.toSeminormedCommRing Complex
                              (@NormedField.toNormedCommRing Complex Complex.instNormedField)))))))))
              (@SeminormedAddGroup.toContinuousENorm Complex
                (@SeminormedAddCommGroup.toSeminormedAddGroup Complex
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@NormedField.toNormedCommRing Complex Complex.instNormedField))))))))
            (ProbabilityTheory.levyCompensatedIntegrand ξ x))
        (@Top.top ENNReal ENNReal.instTop) := by sorry
