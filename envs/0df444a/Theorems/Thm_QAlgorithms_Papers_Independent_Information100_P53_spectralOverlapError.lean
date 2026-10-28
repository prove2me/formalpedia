-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_spectralOverlapError
-- name    : QAlgorithms.Papers.Independent.Information100.P53.spectralOverlapError
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:05:04.894932+00:00
-- url     : https://prove2.me/theorems/31424bd3-13a3-4d85-abac-6748d69f08dc
-- title:
--   Theorem 2: Li spectral-overlap error bound
-- statement:
--   Let $M,N\ge1$, let $S=(\rho_i)_{i=1}^M$ consist of positive semidefinite trace-one matrices on $\mathbb C^N$, and fix $p_i\ge0$ with $\sum_i p_i=1$. Write $P_e(p,S)=1-\sup_D\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, where the supremum ranges over all POVMs $D=(\Lambda_i)_{i=1}^M$. Assume $M\ge2$. For every $i$, choose a complete orthonormal spectral decomposition $\rho_i=\sum_{j=1}^N a_{i,j}|v_{i,j}\rangle\langle v_{i,j}|$ with decreasing eigenvalues, listed with multiplicity, and write $A_{i,j}=|v_{i,j}\rangle\langle v_{i,j}|$. With squared Uhlmann fidelity $F$,
--
--   $$P_e(p,S)\ge\frac{1}{2(M-1)}\sum_{i<k}\sum_{j=1}^N\sum_{l=1}^N\min(p_i a_{i,j},p_k a_{k,l})F(A_{i,j},A_{k,l}).$$
--
--   This cited converse measures pairwise overlaps of the chosen rank-one eigenspaces. Every eigenvector label contributes, including repeated eigenvalues.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 3, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.3, Theorem 2 ([8, Eq.(5)], Li): pairwise rank-one spectral-overlap
lower bound on optimized error. Both eigenvector sums count all N labels,
including zero and repeated eigenvalues. This is a cited background result. -/
theorem spectralOverlapError {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (s : ∀ i, SpectralData (rho i)) :
    (pairSum fun i k => ∑ j : Fin N, ∑ l : Fin N,
      min (p i * (s i).value j) (p k * (s k).value l) *
        fidelity (pureDensity ((s i).basis j)) (pureDensity ((s k).basis l))) /
      (2 * ((M : ℝ) - 1)) ≤ 1 - mixedOptSuccess p rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
