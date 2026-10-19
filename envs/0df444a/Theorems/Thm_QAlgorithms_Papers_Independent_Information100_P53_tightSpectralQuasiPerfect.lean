-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_tightSpectralQuasiPerfect
-- name    : QAlgorithms.Papers.Independent.Information100.P53.tightSpectralQuasiPerfect
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:59:51.07216+00:00
-- url     : https://prove2.me/theorems/33f5dc1d-c89c-4f68-8c9c-33be1b0ca316
-- title:
--   Corollary-3
-- statement:
--   Let $M,N\ge1$, let $\rho_1,\ldots,\rho_M$ be positive semidefinite trace-one operators on $\mathbb C^N$, and fix prior probabilities $p_i\ge0$ with $\sum_i p_i=1$. A decoding POVM $D=(\Lambda_i)$ has positive semidefinite effects summing to the identity. Write $P_c(p,S,D)=\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, $P_e=1-P_c$, and use an omitted decoder to mean optimization over POVMs alone. Let $F$ denote squared Uhlmann fidelity and $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$.
--
--   For each message choose a decreasing spectral decomposition $\rho_i=\sum_{j=1}^N a_{i,j}|a_{i,j}\rangle\langle a_{i,j}|$ with a complete orthonormal eigenbasis, counting multiplicities. Let $I$ be any set of $N$ message/eigenvector pairs such that every selected weight $p_i a_{i,j}$ is at least every unselected weight, and put $B=\sum_{(i,j)\in I}p_i a_{i,j}$. Ties may be resolved arbitrarily.
--
--   If $P_c(p,S)=B$, then there exist a density operator $\mu$ and a real number $t$ such that, writing $P_i^+$ and $P_i^0$ for the strictly positive and zero spectral projections of $\rho_i-t\mu$,
--   $$P_i^+P_j^+=0\quad(i\ne j),\qquad \sum_i(P_i^++P_i^0)\succeq I.$$
--
--   This is exactly the paper's unweighted weak quasi-perfect-code condition. It does not assert that the selected spectral projectors are a POVM.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 4, Corollary-3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.4 and Appendix B-B p.7, Corollary 3: tightness implies precisely the
unweighted weak Definition 1. No converse to Theorem 4's sufficient condition is assumed. -/
theorem tightSpectralQuasiPerfect {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (s : ∀ i, SpectralData (rho i)) (I : Finset (Fin M × Fin N))
    (hI : IsTopSelection N (spectralWeight p s) I)
    (htight : mixedOptSuccess p rho = ∑ z ∈ I, spectralWeight p s z) :
    IsQuasiPerfect rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
