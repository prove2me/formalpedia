-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_loss_under_chaining
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.loss_under_chaining
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:37:05.38264+00:00
-- url     : https://prove2.me/theorems/9a874ac1-3232-42ca-b9b3-ddbc480dd5c9
-- title:
--   channel loss is nondecreasing under chaining
-- statement:
--   Let $\rho$ be a normalized input density on a finite nonzero register, and let $\mathcal N,\mathcal M$ be successive CPTP channels. Define $L(\mathcal N,\rho)=S(\rho)+S_e(\mathcal N,\rho)-S(\mathcal N(\rho))$, with entropy exchange computed on a purification. Then
--
--   $$0\le L(\mathcal N,\rho)\le L(\mathcal M\circ\mathcal N,\rho).$$
--
--   Both losses refer to the original input. This records irreversibility under further processing without access to the discarded environment.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 8, III.D(i), (3.37): channel loss is nondecreasing under chaining

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

/-- PDF p.8, (3.37): composite loss is relative to the ORIGINAL input. -/
theorem loss_under_chaining
    [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop A B) (M : Superop B C) (hN : IsChannel N) (hM : IsChannel M)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    0 ≤ loss N rho ∧ loss N rho ≤ loss (M ∘ N) rho := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
