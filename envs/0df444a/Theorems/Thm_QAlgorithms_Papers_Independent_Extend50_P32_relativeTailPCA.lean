-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_relativeTailPCA
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.relativeTailPCA
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:10:55.98968+00:00
-- url     : https://prove2.me/theorems/26983232-0efd-411d-8132-3a0c17e4e65e
-- title:
--   Unnumbered: PCA within a multiplicative spectral-tail factor
-- statement:
--   Let $d\ge1$ and let $\rho\in\mathbb C^{d\times d}$ be positive semidefinite of trace one, with nonincreasing spectrum $\alpha$. On $n\ge1$ copies the concrete Keyl experiment draws a weak-Schur shape $\lambda$ and then $V\sim K_\lambda(\rho)$. Its rank-$k$ report is $\widehat\rho_k=V\operatorname{diag}(\lambda_1/n,\ldots,\lambda_k/n,0,\ldots,0)V^\dagger$, with no renormalization, for $1\le k\le d$. Write $R_k=\mathbb E D_{H^2}(\widehat\rho_k,\rho)$, where $D_{H^2}(A,B)=\operatorname{Tr}((\sqrt A-\sqrt B)^2)$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. The full report has $k=d$. Fix $\delta>0$ first. There are $C_\delta>0$ and $N_\delta\ge2$, independent of $d,k,n,\rho$, such that the first two clauses hold for $n\ge N_\delta$ in the stated regime. The second is a sufficient-count statement for every such $n$, avoiding an existential choice that could evade the regime. The final clause is unrestricted. All sample-count clauses have $0<\epsilon<1$, choose $n$ before $\rho$, and bound expected error.
--
--   $$
--   \begin{gathered} k\le d/\ln n\ \Longrightarrow\ R_k\le(1+\delta)\alpha_{>k}+C_\delta kd\ln(n)/n,\\ n\ge\left\lceil C_\delta(kd/\epsilon)\ln(d/\epsilon)\right\rceil,\quad k\le d/\ln n\ \Longrightarrow\ R_k\le(1+\delta)\alpha_{>k}+\epsilon,\\ \exists n\le\left\lceil C_\delta(kd/\epsilon)\ln^2(d/\epsilon)\right\rceil:\quad R_k\le(1+\delta)\alpha_{>k}+\epsilon.\end{gathered}
--   $$
--
--   This is a sample-complexity or risk guarantee for the concrete collective measurement and public decoder; it asserts no gate bound.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 7, Unnumbered

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

/-- Unnumbered relative-tail PCA conclusion, PDF pp.7,27-28. For fixed
delta>0 retain the single-log regime risk and its copy bound, separately
from the unrestricted log-squared copy bound. The printed geometric-mean
sentence's second Z2 is read as Z1, as its displayed formulas require.
Copy-complexity clauses use expected error, as the source's discussion does. -/
theorem relativeTailPCA : ∀ delta : ℝ, 0 < delta →
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
    (∀ (d n : ℕ) (hd : 0 < d) (hn : 0 < n), N ≤ n →
      ∀ k : ℕ, 1 ≤ k → k ≤ d → (k : ℝ) ≤ d / Real.log n →
      ∀ (alpha : Fin d → ℝ), Learning.IsDistribution alpha → Antitone alpha →
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho), HasSpectrum rho alpha →
        keylRisk hd hn k rho hRho ≤ ENNReal.ofReal
          ((1 + delta) * tail alpha k + C * k * d * Real.log n / n)) ∧
    (∀ (d : ℕ) (hd : 0 < d) (k : ℕ), 1 ≤ k → k ≤ d →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      (∀ (n : ℕ) (hn : 0 < n), N ≤ n →
        copyBudget C (((k : ℝ) * d / epsilon) * Real.log (d / epsilon)) ≤ n →
        (k : ℝ) ≤ d / Real.log n →
          ∀ (alpha : Fin d → ℝ), Learning.IsDistribution alpha → Antitone alpha →
          ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho), HasSpectrum rho alpha →
            keylRisk hd hn k rho hRho ≤ ENNReal.ofReal ((1 + delta) * tail alpha k + epsilon)) ∧
      (∃ (n : ℕ) (hn : 0 < n), n ≤ copyBudget C (((k : ℝ) * d / epsilon) * Real.log (d / epsilon) ^ 2) ∧
        ∀ (alpha : Fin d → ℝ), Learning.IsDistribution alpha → Antitone alpha →
        ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho), HasSpectrum rho alpha →
          keylRisk hd hn k rho hRho ≤ ENNReal.ofReal ((1 + delta) * tail alpha k + epsilon))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
