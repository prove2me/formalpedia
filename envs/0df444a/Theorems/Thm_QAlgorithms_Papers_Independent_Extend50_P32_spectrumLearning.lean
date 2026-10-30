-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_spectrumLearning
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.spectrumLearning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:37:35.409291+00:00
-- url     : https://prove2.me/theorems/2432f9ad-504c-46ae-bf5e-32589e35ceb5
-- title:
--   Theorem 1.16: Spectrum learning sample complexity
-- statement:
--   Let $d\ge1$ and let $\rho\in\mathbb C^{d\times d}$ be positive semidefinite of trace one, with nonincreasing spectrum $\alpha$. On $n\ge1$ copies the concrete Keyl experiment draws a weak-Schur shape $\lambda$ and then $V\sim K_\lambda(\rho)$. Its rank-$k$ report is $\widehat\rho_k=V\operatorname{diag}(\lambda_1/n,\ldots,\lambda_k/n,0,\ldots,0)V^\dagger$, with no renormalization, for $1\le k\le d$. Write $R_k=\mathbb E D_{H^2}(\widehat\rho_k,\rho)$, where $D_{H^2}(A,B)=\operatorname{Tr}((\sqrt A-\sqrt B)^2)$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. The full report has $k=d$. For every $0<\epsilon<1$, one absolute constant $C>0$ suffices. The positive integer sample count is chosen from $d,k,\epsilon$ before the unknown state or spectrum. The guarantees are expected loss at most $\epsilon$ and success probability at least $2/3$, separately for each indicated metric; integer budgets are rounded upward. No runtime or arbitrary-confidence claim is made. For these spectrum statements use EYD: weak Schur sampling followed by the report $\widehat\alpha=\lambda/n$. For $n\ge1$, put $\bar\lambda=\lambda/n$. Hellinger squared is $\sum_i(\sqrt{a_i}-\sqrt{b_i})^2$, chi-squared is $\sum_i(a_i-b_i)^2/b_i$, and KL is $\sum_i a_i\ln(a_i/b_i)$. The estimate is the first argument, zero-over-zero terms contribute zero, and positive estimated mass at zero true mass gives infinite divergence. A superscript $(k)$ retains only the first $k$ terms, without renormalization.
--
--   $$
--   n\le\left\lceil C\frac{d^2}{\epsilon}\right\rceil,\qquad \mathbb E D(\widehat\alpha,\alpha)\le\epsilon,\quad \Pr\{D(\widehat\alpha,\alpha)\le\epsilon\}\ge\frac23,\quad D\in\{d_{H^2},d_{\mathrm{KL}},d_{\chi^2}\}.
--   $$
--
--   This is a sample-complexity or risk guarantee for the concrete collective measurement and public decoder; it asserts no gate bound.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 6, Theorem 1.16

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

/-- Theorem 1.16, PDF p.6: physical EYD learning, expected error and its
constant-success consequence. The sample count is chosen BEFORE the spectrum;
no confidence amplification or gate complexity is asserted. -/
theorem spectrumLearning : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (hd : 0 < d) (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
      ∃ (n : ℕ) (hn : 0 < n), n ≤ copyBudget C ((d : ℝ) ^ 2 / epsilon) ∧
        ∀ (alpha : Fin d → ℝ) (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
          (metric : FullMetric),
          eydRisk hd hn alpha hAlpha hSorted (fullLoss metric) ≤ ENNReal.ofReal epsilon ∧
          ENNReal.ofReal (2 / 3 : ℝ) ≤ eydSuccess hd hn alpha hAlpha hSorted (fullLoss metric) epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
