-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_schurRowVariance
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.schurRowVariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:54:05.971219+00:00
-- url     : https://prove2.me/theorems/c0d236b0-0181-4216-8f1e-be2d3b3adf33
-- title:
--   Proposition 4.8: Variance of a Schur-Weyl row
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be an arbitrary probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Here $n\ge0$; every row parameter lies in $[d]$. No sortedness is assumed.
--
--   $$
--   \operatorname{Var}(\lambda_k)\le16n.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 19, Proposition 4.8

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

/-- Proposition 4.8, PDF p.19: no sortedness and no n>0 premise. -/
theorem schurRowVariance {d n : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (k : Fin d) : rowVariance alpha n k ≤ 16 * n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
