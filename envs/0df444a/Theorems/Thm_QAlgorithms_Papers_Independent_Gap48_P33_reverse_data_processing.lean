-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_reverse_data_processing
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.reverse_data_processing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:36:11.934971+00:00
-- url     : https://prove2.me/theorems/a64921c3-a611-4efa-a4d5-66bf8f9cd5a2
-- title:
--   reverse data processing
-- statement:
--   Let $\rho$ be a finite-dimensional density and let $\mathcal N:Q\to Q_1$ and $\mathcal M:Q_1\to Q_2$ be CPTP channels. In independent pure-environment dilations let $E_1,E_2$ be the final environments, and $R$ the original purifying reference. Then
--
--   $$I(R:Q_2)\le I(RE_1:Q_2)\le I(RE_1E_2:Q_2)=2S(Q_2).$$
--
--   Equivalently, the first two quantities are $I(\mathcal M\circ\mathcal N,\rho)$ and $I(\mathcal M,\mathcal N(\rho))$. Lean evaluates the latter and the final pure-state information with equivalent canonical purifications. This is the reverse data-processing comparison.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 8, III.D(i), (3.33): reverse data processing

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

/-- PDF p.8, (3.33): RE1 purifies the second-leg input.
An equivalent canonical purification computes this second-leg information.
The final RE1E2:Q2 term is the pure-state value 2 S(Q2). -/
theorem reverse_data_processing
    [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop A B) (M : Superop B C) (hN : IsChannel N) (hM : IsChannel M)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    inputMutualInfo (M ∘ N) rho ≤ inputMutualInfo M (N rho) ∧
    inputMutualInfo M (N rho) ≤ 2 * vnEntropy (M (N rho)) ∧
    mutualInformation (pureDensity (canonicalPurification (M (N rho)))) = 2 * vnEntropy (M (N rho)) := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
