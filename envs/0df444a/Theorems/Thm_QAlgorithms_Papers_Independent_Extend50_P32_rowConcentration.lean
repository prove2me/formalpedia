-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_rowConcentration
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.rowConcentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:09:30.430369+00:00
-- url     : https://prove2.me/theorems/45dc3fe8-f195-42bc-95de-a4837eabd9a4
-- title:
--   Unnumbered: Exponential concentration around each row mean
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be an arbitrary probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. For $n\ge1$, put $\bar\lambda=\lambda/n$. Hellinger squared is $\sum_i(\sqrt{a_i}-\sqrt{b_i})^2$, chi-squared is $\sum_i(a_i-b_i)^2/b_i$, and KL is $\sum_i a_i\ln(a_i/b_i)$. The estimate is the first argument, zero-over-zero terms contribute zero, and positive estimated mass at zero true mass gives infinite divergence. A superscript $(k)$ retains only the first $k$ terms, without renormalization. No sortedness is assumed. The displayed tail bound has $n\ge1$ and threshold $t\ge0$.
--
--   $$
--   \Pr\{|\lambda_k-\mathbb E\lambda_k|\ge t\}\le2\exp\!\left(-\frac{t^2}{8n}\right),\qquad t\ge0.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 19, Unnumbered

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

/-- Exponential concentration displayed in Proposition 4.8's proof,
PDF p.19: no sortedness, t>=0 and n>0. -/
theorem rowConcentration {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (k : Fin d) (t : ℝ) (ht : 0 ≤ t) :
    iidWordEventProbability alpha n (fun w => |row (shape w) k.val - swMean alpha n (fun s => row s k.val)| ≥ t) ≤
      2 * Real.exp (-t ^ 2 / (8 * n)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
