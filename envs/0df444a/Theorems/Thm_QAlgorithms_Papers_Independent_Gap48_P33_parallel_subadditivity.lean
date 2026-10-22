-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_parallel_subadditivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.parallel_subadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:34:24.100267+00:00
-- url     : https://prove2.me/theorems/eb5dae0e-a2bd-4081-842e-3f5a2623052d
-- title:
--   parallel-channel subadditivity
-- statement:
--   Let $\mathcal N_1,\mathcal N_2$ be independent finite-dimensional CPTP channels, and let $\rho_{12}$ be any normalized joint input, including entangled inputs. Write $\rho_1,\rho_2$ for its actual marginals. Then
--
--   $$I(\mathcal N_1\otimes\mathcal N_2,\rho_{12})\le I(\mathcal N_1,\rho_1)+I(\mathcal N_2,\rho_2).$$
--
--   For any finite collection of channels on nonzero registers of possibly different dimensions and any joint density $\rho$, the same statement reads
--
--   $$I\!\left(\bigotimes_i\mathcal N_i,\rho\right)\le\sum_i I(\mathcal N_i,\rho_i).$$
--
--   Each term on the right uses an original input marginal and its purification, rather than another channel's processed output. This bounds information processed in parallel.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 7, III.C, (3.24)–(3.25): parallel-channel subadditivity

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

/-- PDF p.7, (3.24)–(3.25), including the finite-factor extension.
Each right-hand information uses the ORIGINAL marginal and its own purification. -/
theorem parallel_subadditivity
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (N : Superop A B) (M : Superop C D) (hN : IsChannel N) (hM : IsChannel M)
    (rho : Matrix (A × C) (A × C) ℂ) (hrho : IsDensityMatrix rho) :
    (inputMutualInfo (both N M) rho ≤
      inputMutualInfo N (traceRight rho) + inputMutualInfo M (traceLeft rho)) ∧
    (∀ (n : ℕ) (A B : Fin n → Type)
      [instA : ∀ i, Fintype (A i)] [instB : ∀ i, Fintype (B i)]
      [decA : ∀ i, DecidableEq (A i)] [decB : ∀ i, DecidableEq (B i)]
      [neA : ∀ i, Nonempty (A i)] [neB : ∀ i, Nonempty (B i)]
      (P : ∀ i, Superop (A i) (B i)), (∀ i, IsChannel (P i)) →
      ∀ sigma : Matrix (∀ i, A i) (∀ i, A i) ℂ, IsDensityMatrix sigma →
        inputMutualInfo (productChannel P) sigma ≤
          ∑ i, inputMutualInfo (P i) (productMarginal sigma i)) := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
