-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_greene_testing_equivalence
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.greene_testing_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:39:24.239619+00:00
-- url     : https://prove2.me/theorems/43de4a66-e46d-4c18-8525-b7139ba05e86
-- title:
--   Fact 1.6
-- statement:
--   Let $P$ be a closed symmetric property of probability distributions on $[d]$, $d\ge1$, and $0<\epsilon<1$. For every $n\ge0$, a collective quantum $n$-copy tester exists if and only if a classical $n$-sample tester exists that sees only the longest $k$-increasing subsequence lengths, for $1\le k\le d$:
--
--   $$\text{quantum testability}\ \Longleftrightarrow\ \text{testability from the Greene statistics}.$$
--
--   A $k$-increasing subsequence is a union of $k$ disjoint weakly increasing subsequences. Both testers use success probability $2/3$. This is equivalence of attainable guarantees after reduction, rather than pointwise equality of arbitrary effects.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 5, Fact 1.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Fact 1.6, arXiv:1501.05028v1, PDF p.5. Algorithms precede the unknown input; equivalence is existence of testing guarantees. Zero samples are meaningful here. -/
theorem greene_testing_equivalence
    (d n : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ))
    (hP : IsSpectralProperty P) (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    QuantumTestable d n P epsilon ↔ GreeneTestable d n P epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
