-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_filteredWordTailDominance
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.filteredWordTailDominance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:48:54.744969+00:00
-- url     : https://prove2.me/theorems/53d84848-5484-4db9-83e2-384eb5797427
-- title:
--   Theorem 4.2: Filtered-word weak majorization of lower rows
-- statement:
--   Let $w$ be a word over $[d]$, $d\ge1$, and $1\le k\le d$. Let $w^{(k\cdots)}$ be its stable subsequence retaining exactly the letters at least $k$. Weak RSK insertion gives shape $\lambda$. The relation $\unrhd_w$ compares every zero-padded row-prefix sum and does not require equal total sizes.
--
--   $$
--   \operatorname{shRSK}(w^{(k\cdots)})\unrhd_w (\lambda_k,\lambda_{k+1},\ldots),\qquad\lambda=\operatorname{shRSK}(w).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 17, Theorem 4.2

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

/-- Theorem 4.2, PDF pp.16-17: filtered shape WEAKLY dominates the row tail;
no probability assumption, and no equality of total sizes. -/
theorem filteredWordTailDominance {d : ℕ} (hd : 0 < d) (w : List (Fin d))
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    WeakDominates (shape (suffixWord w k)) ((shape w).drop (k - 1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
