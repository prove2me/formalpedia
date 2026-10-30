-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_resource_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.resource_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:13:49.103816+00:00
-- url     : https://prove2.me/theorems/0ef1874b-0aec-4fad-8095-0a6852280c5e
-- title:
--   Lemma 16: overlap of optimized and unoptimized resources
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. For $r$ ports, let $v^{(r)}$ be nonnegative Euclidean-normalized coefficients selected by maximizing the physical deterministic teleportation objective (6), and set $O_r=d^{r/2}\sum_{\lambda\vdash r}v^{(r)}_\lambda P_\lambda/\sqrt{d_\lambda m_\lambda}$ using the actual central character projectors. At $r=0$ this is the scalar identity. Operators on fewer registers are extended by identities. Write $R_{N,d}=|\langle\Phi^+|(O_N\otimes I)|\Phi^+\rangle|$ for the unsquared overlap of the entire unoptimized and optimized resources. Then
--   $$R_{N,d}=d^{-N/2}\sum_{\mu\vdash N}v^{(N)}_\mu\sqrt{d_\mu m_\mu}.$$
--   For qubits, writing $v_l^{(N)}$ for the coefficient of $(N-l,l)$,
--   $$R_{N,2}=2^{-N/2}\sum_{l=0}^{\lfloor N/2\rfloor}v_l^{(N)}(N-2l+1)\sqrt{\frac{\binom{N+1}{l}}{N+1}}.$$
--   Both clauses compare full bipartite resources, not their marginals.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 17, Lemma 16: overlap of optimized and unoptimized resources

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.17, Lemma 16, (89), and corrected (90): root overlap of whole resources.
The qubit prefactor is 2^(-N/2), not printed d^(-(N+1)); (89),(62),(G6) force this correction. -/
theorem resource_overlap (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (v : Schur.Partition d N → ℝ) (hv : IsOptimalCoefficients d N v) :
    resourceFidelity d N (resourceOperation d N v) =
      (∑ mu, v mu * Real.sqrt (irrepDimension mu * Schur.schurDimension mu)) / Real.sqrt ((d : ℝ) ^ N) ∧
    (∀ (w : Schur.Partition 2 N → ℝ), IsOptimalCoefficients 2 N w →
      resourceFidelity 2 N (resourceOperation 2 N w) =
        (∑ l ∈ Finset.range (N / 2 + 1), rowCoefficient N w l *
          ((N : ℝ) - 2 * l + 1) * Real.sqrt ((Nat.choose (N + 1) l : ℝ) / (N + 1 : ℝ))) /
          Real.sqrt ((2 : ℝ) ^ N)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
