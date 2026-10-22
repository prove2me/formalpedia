-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_forward_data_processing
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.forward_data_processing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:35:15.575765+00:00
-- url     : https://prove2.me/theorems/b9856f2f-5920-4108-8e60-de7de074fa38
-- title:
--   forward data processing
-- statement:
--   For a normalized input density $\rho$ and CPTP channels $\mathcal N:Q\to Q_1$, $\mathcal M:Q_1\to Q_2$ between finite nonzero registers, retain the original purifying reference $R$. Then
--
--   $$I(R:Q_2)=I(\mathcal M\circ\mathcal N,\rho)\le I(\mathcal N,\rho)=I(R:Q_1)\le2S(\rho).$$
--
--   The environments are initially independent and discarded after their interactions. This is forward quantum data processing; the source credits its argument to Schumacher and Nielsen [14].
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 8, III.D(i), (3.29): forward data processing

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

-- Reuse only definitions from the pinned accepted library; no imported theorem is used.

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

section FiniteRegisters

variable {A B C D R K J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [Fintype R] [Fintype K] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq R] [DecidableEq K] [DecidableEq J]

/-- PDF pp.7–8, (3.29); its proof is credited to Schumacher–Nielsen [14]. -/
theorem forward_data_processing
    [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop A B) (M : Superop B C) (hN : IsChannel N) (hM : IsChannel M)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    inputMutualInfo (M ∘ N) rho ≤ inputMutualInfo N rho ∧
    inputMutualInfo N rho ≤ 2 * vnEntropy rho := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
