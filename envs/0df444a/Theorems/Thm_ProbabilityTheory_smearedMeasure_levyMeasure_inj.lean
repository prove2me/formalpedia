-- Prove2me | Theorems.Thm_ProbabilityTheory_smearedMeasure_levyMeasure_inj
-- name    : ProbabilityTheory.smearedMeasure_levyMeasure_inj
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:03:50.891423+00:00
-- url     : https://prove2.me/theorems/f4a35c15-a66a-4caf-b8cf-4e633300338c
-- title:
--   LeanLevy: ProbabilityTheory.smearedMeasure_levyMeasure_inj
-- statement:
--   **Recovery of the Lévy measure.** If two smeared measures agree, the Lévy measures agree: Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineUniqueness.lean#L473

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

theorem ProbabilityTheory.smearedMeasure_levyMeasure_inj : ∀ {ν₁ ν₂ : @MeasureTheory.Measure Real Real.measurableSpace},
  ProbabilityTheory.IsLevyMeasure ν₁ →
    ProbabilityTheory.IsLevyMeasure ν₂ →
      ∀ {σ₁ σ₂ : NNReal},
        @Eq (@MeasureTheory.Measure Real Real.measurableSpace) (ProbabilityTheory.smearedMeasure σ₁ ν₁)
            (ProbabilityTheory.smearedMeasure σ₂ ν₂) →
          @Eq (@MeasureTheory.Measure Real Real.measurableSpace) ν₁ ν₂ := by sorry
