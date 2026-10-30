-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_rankSensitiveKeylRisk
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.rankSensitiveKeylRisk
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:03:18.44407+00:00
-- url     : https://prove2.me/theorems/8eb3a724-5be2-4f8b-9dc3-521d5c497336
-- title:
--   Theorem 5.7: Rank-sensitive full Keyl tomography risk
-- statement:
--   Let $d\ge1$ and let $\rho\in\mathbb C^{d\times d}$ be positive semidefinite of trace one, with nonincreasing spectrum $\alpha$. On $n\ge1$ copies the concrete Keyl experiment draws a weak-Schur shape $\lambda$ and then $V\sim K_\lambda(\rho)$. Its rank-$k$ report is $\widehat\rho_k=V\operatorname{diag}(\lambda_1/n,\ldots,\lambda_k/n,0,\ldots,0)V^\dagger$, with no renormalization, for $1\le k\le d$. Write $R_k=\mathbb E D_{H^2}(\widehat\rho_k,\rho)$, where $D_{H^2}(A,B)=\operatorname{Tr}((\sqrt A-\sqrt B)^2)$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. The full report has $k=d$. There are absolute positive constants and an absolute integer threshold $N\ge2$ such that the following bound holds uniformly for every $n\ge N$. Here $r=\operatorname{rank}(\rho)$ is the actual rank, not an independent accuracy certificate.
--
--   $$
--   R_d\le C\frac{rd}{n}\min\{r,\ln n\},\qquad r=\operatorname{rank}(\rho).
--   $$
--
--   This is a sample-complexity or risk guarantee for the concrete collective measurement and public decoder; it asserts no gate bound.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 26, Theorem 5.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Matrix ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Extend50.P32

open QAlgorithms.Papers.Independent.Support50.P38 (wordMass tv)

-- For the density matrices below, the characteristic-polynomial identity
-- preserves all eigenvalues with multiplicity and is equivalent to unitary
-- diagonalization with these real eigenvalues. No accuracy is assumed.

open QAlgorithms.Papers.Independent.Gap20.P17 (HasSpectrum)

/-- Theorem 5.7, PDF pp.26-27: r is the ACTUAL rank. Uniform constants
and an absolute n-threshold >=2 reflect the source O-bound. -/
theorem rankSensitiveKeylRisk : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
    ∀ (d n : ℕ) (hd : 0 < d) (hn : 0 < n), N ≤ n →
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho),
        keylRisk hd hn d rho hRho ≤ ENNReal.ofReal
          (C * (rho.rank : ℝ) * d / n * min (rho.rank : ℝ) (Real.log n)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
