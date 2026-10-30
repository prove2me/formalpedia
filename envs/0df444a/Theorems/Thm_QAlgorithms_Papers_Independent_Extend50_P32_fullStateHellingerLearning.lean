-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_fullStateHellingerLearning
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.fullStateHellingerLearning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:38:18.445807+00:00
-- url     : https://prove2.me/theorems/ef29d140-1b66-4985-8ebb-2fdfc4cf192e
-- title:
--   Theorem 1.17: Full-state Hellinger tomography
-- statement:
--   Let $d\ge1$ and let $\rho\in\mathbb C^{d\times d}$ be positive semidefinite of trace one, with nonincreasing spectrum $\alpha$. On $n\ge1$ copies the concrete Keyl experiment draws a weak-Schur shape $\lambda$ and then $V\sim K_\lambda(\rho)$. Its rank-$k$ report is $\widehat\rho_k=V\operatorname{diag}(\lambda_1/n,\ldots,\lambda_k/n,0,\ldots,0)V^\dagger$, with no renormalization, for $1\le k\le d$. Write $R_k=\mathbb E D_{H^2}(\widehat\rho_k,\rho)$, where $D_{H^2}(A,B)=\operatorname{Tr}((\sqrt A-\sqrt B)^2)$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. The full report has $k=d$. For every $0<\epsilon<1$, one absolute constant $C>0$ suffices. The positive integer sample count is chosen from $d,k,\epsilon$ before the unknown state or spectrum. The guarantees are expected loss at most $\epsilon$ and success probability at least $2/3$, separately for each indicated metric; integer budgets are rounded upward. No runtime or arbitrary-confidence claim is made.
--
--   $$
--   n\le\left\lceil C\min\left\{\frac{d^2}{\epsilon}\ln\frac d\epsilon,\frac{d^3}{\epsilon}\right\}\right\rceil,\qquad R_d\le\epsilon,\quad\Pr\{D_{H^2}(\widehat\rho_d,\rho)\le\epsilon\}\ge\frac23.
--   $$
--
--   This is a sample-complexity or risk guarantee for the concrete collective measurement and public decoder; it asserts no gate bound.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 6, Theorem 1.17

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

/-- Theorem 1.17, PDF p.6 (seed PDF p.1; expected-risk input Theorem 5.7,
p.26). Uniform full-state Keyl learning; integer sample budgets are rounded
up. Constants and the experiment precede rho. This is copy, not gate, complexity. -/
theorem fullStateHellingerLearning : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (hd : 0 < d) (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
      ∃ (n : ℕ) (hn : 0 < n), n ≤ copyBudget C
        (min (((d : ℝ) ^ 2 / epsilon) * Real.log (d / epsilon)) ((d : ℝ) ^ 3 / epsilon)) ∧
        ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho),
          keylRisk hd hn d rho hRho ≤ ENNReal.ofReal epsilon ∧
          ENNReal.ofReal (2 / 3 : ℝ) ≤ keylSuccess hd hn d rho hRho epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
