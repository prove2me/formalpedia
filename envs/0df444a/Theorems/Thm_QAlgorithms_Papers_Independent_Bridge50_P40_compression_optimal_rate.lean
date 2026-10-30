-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_compression_optimal_rate
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.compression_optimal_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:07:41.136241+00:00
-- url     : https://prove2.me/theorems/c0f600f9-1cc0-4988-b1a8-4d3b1e6f1ba9
-- title:
--   Optimal Schumacher compression rate and weak converse (Schumacher)
-- statement:
--   All registers are finite and nonempty, all source kets have unit norm, all density operators are positive semidefinite with trace one, logarithms are base two, and F denotes root fidelity. Fix a density operator $\rho^A$ and its normalized purification $\psi^{RA}$. A feasible block pair $(r_n,f_n)$ is computed from arbitrary CPTP encoding $\mathcal C:A^n\to\mathbb C^d$ and decoding $\mathcal D:\mathbb C^d\to A^n$, with positive integer $d$, rate $r_n=\log_2 d/n$, and root fidelity $f_n$ between the same purification target and the output with identity on $R^n$. A rate $r$ is achievable when feasible pairs exist for every positive $n$, with $r_n\to r$ and $f_n\to1$. Then
--
--   $$\min\{r:r\text{ is achievable}\}=S(\rho).$$
--
--   The minimum is an achievable asymptotic rate. For each fixed ceiling $c<S(\rho)$ there exist $\epsilon>0$ and $N$ such that every $n\ge N$, $n>0$, and every feasible pair $(r,f)$ with $r\le c$ obey $f\le1-\epsilon$.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 12, Theorem 12

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.12, Theorem 12 (Schumacher [33]): minimum achievable compression
rate and weak converse in Definition 3's reference-entangled fidelity model. -/
theorem compression_optimal_rate {A R : Type} [Fintype A] [Fintype R]
    [Nonempty A] [Nonempty R]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × A)) (hpsi : IsState psi)
    (hpur : traceLeft (pureDensity psi) = rho) :
    IsLeast {rate : ℝ | SourceProtocolAchievable (CompressionRateFidelity psi) rate}
      (vnEntropy rho) ∧
    (∀ ceiling : ℝ, ceiling < vnEntropy rho → ∃ eps : ℝ, 0 < eps ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → 0 < n → ∀ rate fidelity : ℝ,
        CompressionRateFidelity psi n rate fidelity → rate ≤ ceiling →
          fidelity ≤ 1 - eps) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
