-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_rankKTailTomography
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.rankKTailTomography
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:40:23.366821+00:00
-- url     : https://prove2.me/theorems/816c331e-5bab-4615-a511-447b3337379f
-- title:
--   Theorem 1.19: Rank-k tomography with spectral-tail error
-- statement:
--   Let $d\ge1$ and let $\rho\in\mathbb C^{d\times d}$ be positive semidefinite of trace one, with nonincreasing spectrum $\alpha$. On $n\ge1$ copies the concrete Keyl experiment draws a weak-Schur shape $\lambda$ and then $V\sim K_\lambda(\rho)$. Its rank-$k$ report is $\widehat\rho_k=V\operatorname{diag}(\lambda_1/n,\ldots,\lambda_k/n,0,\ldots,0)V^\dagger$, with no renormalization, for $1\le k\le d$. Write $R_k=\mathbb E D_{H^2}(\widehat\rho_k,\rho)$, where $D_{H^2}(A,B)=\operatorname{Tr}((\sqrt A-\sqrt B)^2)$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. The full report has $k=d$. There are absolute positive constants and an absolute integer threshold $N\ge2$ such that the following bound holds uniformly for every $n\ge N$.
--
--   $$
--   \operatorname{rank}(\widehat\rho_k)\le k,\qquad R_k\le\alpha_{>k}+C_1\frac{kdL}{n}+C_2 kL\sqrt{\frac{\alpha_{>k}}n},\qquad L=\min\{k,\ln n\}.
--   $$
--
--   This is a sample-complexity or risk guarantee for the concrete collective measurement and public decoder; it asserts no gate bound.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 7, Theorem 1.19

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

/-- Theorem 1.19, PDF p.7: concrete rank-k Keyl report. k*L is OUTSIDE
the square root. An absolute threshold >=2 gives the intended O-bound
rather than the false literal zero error at n=1. -/
theorem rankKTailTomography : ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (d n : ℕ) (hd : 0 < d) (hn : 0 < n), N ≤ n →
      ∀ (alpha : Fin d → ℝ), Learning.IsDistribution alpha → Antitone alpha →
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho), HasSpectrum rho alpha →
      ∀ k : ℕ, 1 ≤ k → k ≤ d →
        (∀ (s : Schur.Partition d n) (U : Matrix.unitaryGroup (Fin d) ℂ),
          (truncatedReport hd hn k s U).rank ≤ k) ∧
        keylRisk hd hn k rho hRho ≤ ENNReal.ofReal
          (tail alpha k + C1 * k * d * min (k : ℝ) (Real.log n) / n +
            C2 * k * min (k : ℝ) (Real.log n) * Real.sqrt (tail alpha k / n)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
