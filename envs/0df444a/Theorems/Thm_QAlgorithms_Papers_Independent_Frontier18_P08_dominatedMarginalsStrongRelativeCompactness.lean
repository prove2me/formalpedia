-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P08_dominatedMarginalsStrongRelativeCompactness
-- name    : QAlgorithms.Papers.Independent.Frontier18.P08.dominatedMarginalsStrongRelativeCompactness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:56:48.359322+00:00
-- url     : https://prove2.me/theorems/4db98a90-290a-4e20-b067-a58961570c32
-- title:
--   Lemma 7: strong relative compactness from two dominated output marginals
-- statement:
--   Let $H_A,H_B,H_C$ be separable complex Hilbert spaces, let $\rho_A$ be a normalized trace-class state with trivial kernel, and let $(\Phi_n)$ be completely positive, complex-linear, trace-nonincreasing maps from the full trace-class space on $H_A$ to that on $H_B\otimes H_C$. Suppose there are fixed positive trace-class operators $\rho_B,\rho_C$ such that
--
--   $$
--   \operatorname{Tr}_C\Phi_n(\rho_A)\le\rho_B,
--   \qquad \operatorname{Tr}_B\Phi_n(\rho_A)\le\rho_C
--   \quad\text{for every }n.
--   $$
--
--   The range of $(\Phi_n)$ is relatively compact for strong convergence: every sequence in this range has a subsequence converging in trace norm on every input state to a quantum operation of the same type.
--
--   This gives the compactness needed to extract recovery operations while controlling only two output marginals. The bounds need not have trace one, and trivial kernel does not require a bounded inverse.
--
--   **Formalization Note** The conclusion uses the sequential relative-compactness criterion for the source strong topology on operations between separable systems. The reindexing is arbitrary, and the further subsequence is strictly increasing.
-- source:
--   Measures of quantum correlations in infinite-dimensional systems, arXiv:1506.06377v2, PDF p. 46, Lemma 7: strong relative compactness from two dominated output marginals

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08

noncomputable section

open Filter

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P08

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

/-- Lemma 7, PDF p.46: relative compactness in the strong operation topology.
We use its sequential criterion: EVERY sequence in the range has a further
subsequence converging strongly to an operation. The source strong topology
on operations between separable Hilbert spaces is metrizable (§8.2, p.41).
Both dominating marginals are arbitrary positive trace-class operators. -/
theorem dominatedMarginalsStrongRelativeCompactness
    {I J K : Type} [Countable I] [Countable J] [Countable K]
    (rhoA : Accepted.State I) (hFull : HasFullSupport rhoA)
    (Phi : ℕ → (Matrix I I ℂ → Matrix (J × K) (J × K) ℂ))
    (hPhi : ∀ n, IsQuantumOperation (Phi n))
    (rhoB : Matrix J J ℂ) (hB : PositiveTraceClass rhoB)
    (rhoC : Matrix K K ℂ) (hC : PositiveTraceClass rhoC)
    (hDomB : ∀ n, OperatorBelow (partialTraceSecond (Phi n rhoA.coefficients)) rhoB)
    (hDomC : ∀ n, OperatorBelow (partialTraceFirst (Phi n rhoA.coefficients)) rhoC) :
    ∀ r : ℕ → ℕ, ∃ s : ℕ → ℕ, StrictMono s ∧
      ∃ Phi0 : Matrix I I ℂ → Matrix (J × K) (J × K) ℂ,
        IsQuantumOperation Phi0 ∧ StronglyConverges (fun k => Phi (r (s k))) Phi0 := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P08

end
