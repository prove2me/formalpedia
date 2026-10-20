-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_mixtureLogRank
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.mixtureLogRank
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:55:34.529926+00:00
-- url     : https://prove2.me/theorems/86ff7d82-052a-4ec3-aebb-544499e25f08
-- title:
--   Log-rank bound for finite sums
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $N\ge1$, let $\rho_A^1,\ldots,\rho_A^N$ be positive semidefinite operators, and let $p_1,\ldots,p_N$ be real coefficients such that $\rho_A=\sum_{j=1}^Np_j\rho_A^j$ is positive semidefinite. Normalization is unnecessary. With $H_0(A)_\sigma=\log_2\operatorname{rank}\sigma$ and $\log_2 0=-\infty$, $$H_0(A)_\rho\le\max_{1\le j\le N}H_0(A)_{\rho^j}+\log_2N.$$
--
--   This bounds the support size of a finite mixture, including zero summands and the zero mixture.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 20, Lemma 26

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1108.5357v3, PDF p.20, Lemma 26, (A2).
No normalization of the positive operators or coefficients is needed for this rank bound. -/
theorem mixtureLogRank {A : Type*} [Fintype A] [Nonempty A]
    (N : ℕ) (hN : 0 < N) (p : Fin N → ℝ) (rho : Fin N → Op A)
    (hrho : ∀ j, (rho j).PosSemidef)
    (hmix : (∑ j, (p j : ℂ) • rho j).PosSemidef) :
    logRank (∑ j, (p j : ℂ) • rho j) ≤
      (⨆ j, logRank (rho j)) + (Real.logb 2 (N : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
