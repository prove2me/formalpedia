-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_rskOneLetterSensitivity
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.rskOneLetterSensitivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:41:34.342806+00:00
-- url     : https://prove2.me/theorems/b0333ee4-3db0-4fee-a62e-7633cb914607
-- title:
--   Proposition 2.2: RSK sensitivity to one edited letter
-- statement:
--   Let $d\ge1$ and let $w,w^\prime\in[d]^n$ differ in exactly one coordinate. Write $\lambda=\operatorname{shRSK}(w)$ and $\lambda^\prime=\operatorname{shRSK}(w^\prime)$, using weak insertion and zero-padded rows, and let $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$.
--
--   $$
--   |\lambda_{\le k}-\lambda^\prime_{\le k}|\le1,\qquad |\lambda_k-\lambda^\prime_k|\le2\quad(1\le k\le d).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 11, Proposition 2.2

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

/-- Proposition 2.2, PDF p.11: absolute values on BOTH inequalities;
subtraction takes place in the reals. -/
theorem rskOneLetterSensitivity {d n : ℕ} (hd : 0 < d) (w v : Fin n → Fin d)
    (hedit : ∃ t, w t ≠ v t ∧ ∀ i, i ≠ t → w i = v i) :
    ∀ k : Fin d,
      |rowPrefix (shape (List.ofFn w)) (k.val + 1) - rowPrefix (shape (List.ofFn v)) (k.val + 1)| ≤ 1 ∧
      |row (shape (List.ofFn w)) k.val - row (shape (List.ofFn v)) k.val| ≤ 2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
