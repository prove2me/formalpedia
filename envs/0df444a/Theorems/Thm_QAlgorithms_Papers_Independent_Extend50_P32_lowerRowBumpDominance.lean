-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_lowerRowBumpDominance
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.lowerRowBumpDominance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:35:34.650691+00:00
-- url     : https://prove2.me/theorems/8ba25b81-8164-4ade-8fea-27d422db0a0f
-- title:
--   Theorem 1.12: Lower-row bump-order majorization
-- statement:
--   Let $x$ be a finite word over any linearly ordered alphabet and let $k\ge1$. During weak RSK insertion let $x^{(k)}$ list, in bump order, the occurrences bumped from row $k$ into row $k+1$. Let $\bar x$ retain exactly these occurrences in their original order. Dominance $\unrhd$ means every row prefix is at least as large and total sizes agree; repeated letter values retain their distinct occurrence identities.
--
--   $$
--   \operatorname{shRSK}(\bar x)\unrhd\operatorname{shRSK}(x^{(k)}).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 4, Theorem 1.12

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

/-- Theorem 1.12, PDF p.4: source row k is internal row k-1.
Occurrence IDs distinguish repeated letters. Restated as Theorem 6.3. -/
theorem lowerRowBumpDominance {A : Type*} [LinearOrder A] (x : List A)
    (k : ℕ) (hk : 1 ≤ k) :
    shapeDominates (shape (originalBumpedWord x (k - 1))) (shape (bumpedWord x (k - 1))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
