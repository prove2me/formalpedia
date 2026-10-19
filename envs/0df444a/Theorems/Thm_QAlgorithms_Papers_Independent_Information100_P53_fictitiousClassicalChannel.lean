-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_fictitiousClassicalChannel
-- name    : QAlgorithms.Papers.Independent.Information100.P53.fictitiousClassicalChannel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:01:49.510871+00:00
-- url     : https://prove2.me/theorems/5a411e77-a2e3-4a3a-9b01-bafbea7afa13
-- title:
--   fictitious-classical-channel
-- statement:
--   Let $M,N\ge1$, let $\rho_1,\ldots,\rho_M$ be positive semidefinite trace-one operators on $\mathbb C^N$, and fix prior probabilities $p_i\ge0$ with $\sum_i p_i=1$. A decoding POVM $D=(\Lambda_i)$ has positive semidefinite effects summing to the identity. Write $P_c(p,S,D)=\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, $P_e=1-P_c$, and use an omitted decoder to mean optimization over POVMs alone. Let $F$ denote squared Uhlmann fidelity and $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$.
--
--   For each message choose a decreasing spectral decomposition $\rho_i=\sum_{j=1}^N a_{i,j}|a_{i,j}\rangle\langle a_{i,j}|$ with a complete orthonormal eigenbasis, counting multiplicities. Let $I$ be any set of $N$ message/eigenvector pairs such that every selected weight $p_i a_{i,j}$ is at least every unselected weight, and put $B=\sum_{(i,j)\in I}p_i a_{i,j}$. Ties may be resolved arbitrarily.
--
--   There exist permutations $\sigma_i$ of the $N$ spectral entries such that exactly one pair $(i,\sigma_i(j))$ is selected for each column $j$. Define the fictitious classical channel $W_{i,j}=a_{i,\sigma_i(j)}$. Its fixed-prior optimal decoding success satisfies
--   $$\sum_{j=1}^N\max_i p_iW_{i,j}=B,\qquad P_c(p,S)\le\sum_{j=1}^N\max_i p_iW_{i,j}.$$
--
--   This realizes the spectral bound as classical MAP success. In product applications its rows are messages; independent row permutations need not define a memoryless symbol channel.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 4, fictitious-classical-channel

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF pp.4–5, fictitious-channel interpretation: row permutations put exactly one
selected entry in each column; fixed-prior MAP success equals the spectral bound.
The quantum success is only bounded above by that classical quantity. -/
theorem fictitiousClassicalChannel {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (s : ∀ i, SpectralData (rho i)) (I : Finset (Fin M × Fin N))
    (hI : IsTopSelection N (spectralWeight p s) I) :
    ∃ sigma : Fin M → Equiv.Perm (Fin N),
      (∀ j, ∃! i, (i, sigma i j) ∈ I) ∧
      classicalSuccess p (fun i j => (s i).value (sigma i j)) =
        ∑ z ∈ I, spectralWeight p s z ∧
      mixedOptSuccess p rho ≤ classicalSuccess p (fun i j => (s i).value (sigma i j)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
