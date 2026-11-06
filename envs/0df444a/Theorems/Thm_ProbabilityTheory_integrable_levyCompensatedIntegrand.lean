-- Prove2me | Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
-- name    : ProbabilityTheory.integrable_levyCompensatedIntegrand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:22:41.323378+00:00
-- url     : https://prove2.me/theorems/3253c80e-2e5e-4a65-be86-fb137253f5ec
-- title:
--   LeanLevy: ProbabilityTheory.integrable_levyCompensatedIntegrand
-- statement:
--   The compensated integrand is Bochner integrable against a Lévy measure. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CompensatedIntegral.lean#L163

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

theorem ProbabilityTheory.integrable_levyCompensatedIntegrand : ∀ {ν : @MeasureTheory.Measure Real Real.measurableSpace},
  ProbabilityTheory.IsLevyMeasure ν →
    ∀ (ξ : Real),
      @MeasureTheory.Integrable Complex
        (@UniformSpace.toTopologicalSpace Complex
          (@PseudoMetricSpace.toUniformSpace Complex
            (@SeminormedRing.toPseudoMetricSpace Complex
              (@SeminormedCommRing.toSeminormedRing Complex
                (@NormedCommRing.toSeminormedCommRing Complex
                  (@NormedField.toNormedCommRing Complex Complex.instNormedField))))))
        (@SeminormedAddGroup.toContinuousENorm Complex
          (@SeminormedAddCommGroup.toSeminormedAddGroup Complex
            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@NormedField.toNormedCommRing Complex Complex.instNormedField)))))))
        Real Real.measurableSpace (ProbabilityTheory.levyCompensatedIntegrand ξ) ν := by sorry
