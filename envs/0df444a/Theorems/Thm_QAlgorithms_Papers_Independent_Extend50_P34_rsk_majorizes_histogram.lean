-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_rsk_majorizes_histogram
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.rsk_majorizes_histogram
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:48:17.742517+00:00
-- url     : https://prove2.me/theorems/6ec02fa2-e5d9-4df7-8e53-e825814727be
-- title:
--   Proposition 2.15
-- statement:
--   For a word $w\in[d]^n$, let $\lambda=\operatorname{RSK}(w)$ and let $c_i(w)$ be its letter counts. Then $|\lambda|=n$ and $\lambda$ majorizes the decreasing rearrangement of the histogram:
--
--   $$\sum_{i=1}^k c_i^{\downarrow}(w)\le\sum_{i=1}^k\lambda_i\qquad(0\le k\le d).$$
--
--   Equivalently the inequality holds for the sum over every set of $k$ letters. This formulation avoids assuming that the RSK shape of a fixed word is invariant under relabelling.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 16, Proposition 2.15

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 2.15, arXiv:1501.05028v1, PDF p.16. The largest k frequencies are represented by all k-letter subsets. Equal total size is stated, including n=0. -/
theorem rsk_majorizes_histogram
    (d n : ℕ) (hd : 0 < d) (w : Fin n → Fin d) :
    (rsk w).card = n ∧
      ∀ k : ℕ, k ≤ d → ∀ S : Finset (Fin d), S.card = k →
        (∑ i ∈ S, counts w i) ≤ ∑ i ∈ Finset.range k, (rsk w).rowLen i := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
