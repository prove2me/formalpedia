-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_measurementRelativeEntropyMonotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.measurementRelativeEntropyMonotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:10:57.649713+00:00
-- url     : https://prove2.me/theorems/b46218af-eb73-4083-8f75-02fb3ea58486
-- title:
--   Section 4, printed 3.2: measurement relative-entropy bound (14)
-- statement:
--   For finite nonzero input and outcome spaces, a POVM $(E_j)$, and arbitrary density matrices $D_1,D_2$, let $\mu_i(j)=\operatorname{Tr}(D_iE_j)$. Then
--
--   $$S(\mu_1,\mu_2)\le S(D_1,D_2).$$
--
--   Classical entropy is the extended Umegaki entropy of the computed diagonal law. Zero effects, zero probabilities, singular reference states and infinite relative entropy are allowed.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 6, Section 4, printed 3.2: measurement relative-entropy bound (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.6, (14).
All finite POVMs are allowed, including zero effects; relative entropy uses its
support-failure value +infinity. No invertibility assumption is imposed. -/
theorem measurementRelativeEntropyMonotonicity {I O : Type*}
    [Fintype I] [Fintype O] [Nonempty I] [Nonempty O]
    (E : O → Matrix I I ℂ) (hE : IsPOVM E)
    (D1 D2 : Matrix I I ℂ)
    (hD1 : IsDensityMatrix D1) (hD2 : IsDensityMatrix D2) :
    QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
      (measurementDensity E D1) (measurementDensity E D2) ≤
      QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy D1 D2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
