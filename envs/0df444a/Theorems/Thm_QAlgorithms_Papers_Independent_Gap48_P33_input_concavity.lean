-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_input_concavity
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.input_concavity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:32:24.678978+00:00
-- url     : https://prove2.me/theorems/db1d2bbd-8228-484e-8a65-5d0ec52c810d
-- title:
--   input concavity
-- statement:
--   Fix a CPTP channel $\mathcal N$ between finite nonzero registers. Let $(w_j)$ be any finite probability vector and let $\rho_j$ be normalized input densities. With $I(\mathcal N,\rho)$ denoting reference-output mutual information for a purification of $\rho$,
--
--   $$\sum_j w_j I(\mathcal N,\rho_j)\le I\!\left(\mathcal N,\sum_j w_j\rho_j\right).$$
--
--   The channel is fixed across the mixture, while the purification is constructed for each input. This is concavity of the processed information in the input density.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 6, III.C, (3.17): input concavity

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

/-- PDF p.6, (3.17): input concavity for a FIXED channel; purifications vary with input. -/
theorem input_concavity
    [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (w : J → ℝ) (hw : ProbabilityWeights w)
    (rho : J → Matrix A A ℂ) (hrho : ∀ j, IsDensityMatrix (rho j)) :
    (∑ j, w j * inputMutualInfo N (rho j)) ≤ inputMutualInfo N (average w rho) := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
