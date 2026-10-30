-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_uniformRowMSE
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.uniformRowMSE
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:31:45.215796+00:00
-- url     : https://prove2.me/theorems/f2864c46-0ef6-48af-9e28-ec01a11b8b39
-- title:
--   Theorem 1.5: Uniform row mean squared error
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Here $n\ge0$; every row parameter lies in $[d]$. The constant $C>0$ is absolute and precedes all dimensions, sample counts, spectra and states.
--
--   $$
--   \exists C>0\ \forall d,n,\alpha,k:\quad \mathbb E(\lambda_k-\alpha_k n)^2\le C\min\{1,d\alpha_k\}\,n.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 3, Theorem 1.5

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

/-- Theorem 1.5, PDF p.3: the O-constant is absolute, not instance dependent. -/
theorem uniformRowMSE : ∃ C : ℝ, 0 < C ∧
    ∀ (d n : ℕ), 0 < d → ∀ alpha : Fin d → ℝ,
      Learning.IsDistribution alpha → Antitone alpha → ∀ k : Fin d,
        rowMSE alpha n k ≤ C * rowScale alpha k * n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
