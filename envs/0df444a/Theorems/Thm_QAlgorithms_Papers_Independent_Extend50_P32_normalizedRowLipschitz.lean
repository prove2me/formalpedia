-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_normalizedRowLipschitz
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.normalizedRowLipschitz
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:42:16.248043+00:00
-- url     : https://prove2.me/theorems/424c0670-78f4-4db1-b1e4-7945bbfc6597
-- title:
--   Proposition 2.4: Distributional Lipschitz continuity of normalized rows
-- statement:
--   Let $d\ge1$, $n\ge1$, and let $\alpha,\alpha^\prime$ be arbitrary probability vectors on $[d]$, with no ordering assumption. Let $\lambda\sim\mathrm{SW}^n(\alpha)$ and $\lambda^\prime\sim\mathrm{SW}^n(\alpha^\prime)$ and put $\bar\lambda=\lambda/n$, $\bar\lambda^\prime=\lambda^\prime/n$. Prefixes sum the first $k$ rows, for $1\le k\le d$, and $d_{\mathrm{TV}}(\alpha,\alpha^\prime)=\tfrac12\sum_i|\alpha_i-\alpha_i^\prime|$.
--
--   $$
--   |\mathbb E\bar\lambda_{\le k}-\mathbb E\bar\lambda^\prime_{\le k}|\le d_{\mathrm{TV}}(\alpha,\alpha^\prime),\qquad |\mathbb E\bar\lambda_k-\mathbb E\bar\lambda^\prime_k|\le2d_{\mathrm{TV}}(\alpha,\alpha^\prime).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 11, Proposition 2.4

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

/-- Proposition 2.4, PDF p.11: normalized rows; NO sortedness assumption. -/
theorem normalizedRowLipschitz {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (alpha beta : Fin d → ℝ) (hAlpha : Learning.IsDistribution alpha)
    (hBeta : Learning.IsDistribution beta) : ∀ k : Fin d,
    |swMean alpha n (fun s => rowPrefix s (k.val + 1) / n) -
      swMean beta n (fun s => rowPrefix s (k.val + 1) / n)| ≤ tv alpha beta ∧
    |swMean alpha n (fun s => row s k.val / n) -
      swMean beta n (fun s => row s k.val / n)| ≤ 2 * tv alpha beta := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
