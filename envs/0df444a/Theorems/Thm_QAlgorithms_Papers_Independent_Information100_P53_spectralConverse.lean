-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_spectralConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P53.spectralConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:52:34.763097+00:00
-- url     : https://prove2.me/theorems/bd3b2a47-ca3c-4340-b427-d448328602ba
-- title:
--   Theorem 4 (Spectral converse); seed paper result
-- statement:
--   Let $M,N\ge1$, let $\rho_1,\ldots,\rho_M$ be positive semidefinite trace-one operators on $\mathbb C^N$, and fix prior probabilities $p_i\ge0$ with $\sum_i p_i=1$. A decoding POVM $D=(\Lambda_i)$ has positive semidefinite effects summing to the identity. Write $P_c(p,S,D)=\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, $P_e=1-P_c$, and use an omitted decoder to mean optimization over POVMs alone. Let $F$ denote squared Uhlmann fidelity and $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$.
--
--   For each message choose a decreasing spectral decomposition $\rho_i=\sum_{j=1}^N a_{i,j}|a_{i,j}\rangle\langle a_{i,j}|$ with a complete orthonormal eigenbasis, counting multiplicities. Let $I$ be any set of $N$ message/eigenvector pairs such that every selected weight $p_i a_{i,j}$ is at least every unselected weight, and put $B=\sum_{(i,j)\in I}p_i a_{i,j}$. Ties may be resolved arbitrarily.
--
--   For every decoding POVM,
--   $$P_c(p,S,D)\le B\le1.$$
--   The first inequality is an equality whenever $\Lambda_i=\sum_{j:(i,j)\in I}|a_{i,j}\rangle\langle a_{i,j}|$ for every message, provided these effects form the specified POVM.
--
--   This bounds discrimination using only the spectra and the fixed prior.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 4, Theorem 4 (Spectral converse); seed paper result

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.4 and Appendix B-A p.7, Theorem 4 (Spectral converse), including both
inequalities and the sufficient equality clause; the decoder remains a POVM. -/
theorem spectralConverse {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (s : ∀ i, SpectralData (rho i)) (I : Finset (Fin M × Fin N))
    (hI : IsTopSelection N (spectralWeight p s) I)
    (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    success p rho D ≤ ∑ z ∈ I, spectralWeight p s z ∧
    (∑ z ∈ I, spectralWeight p s z) ≤ 1 ∧
    ((∀ i, D i = selectedProjector s I i) →
      success p rho D = ∑ z ∈ I, spectralWeight p s z) := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
