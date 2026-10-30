-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_classical_lower_bound_transfers
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.classical_lower_bound_transfers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:40:05.923508+00:00
-- url     : https://prove2.me/theorems/ff8bf599-dc37-4726-abbc-ac08199d42b2
-- title:
--   Fact 1.7
-- statement:
--   Let $P$ be a closed permutation-invariant property of distributions on $[d]$, where $d\ge1$, and let $0<\epsilon<1$. Suppose every classical $\epsilon$-tester with success probability $2/3$ uses at least $f(d,\epsilon)$ samples. Then every collective quantum tester of the corresponding spectral property satisfies
--
--   $$n\ge f(d,\epsilon).$$
--
--   The tester is fixed before the input state. This transfers any valid classical lower bound to quantum copy complexity.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 5, Fact 1.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Fact 1.7, arXiv:1501.05028v1, PDF p.5.  -/
theorem classical_lower_bound_transfers
    (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ))
    (hP : IsSpectralProperty P) (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1)
    (f : ℕ → ℝ → ℝ)
    (hLower : ∀ n, ClassicalTestable d n P epsilon → f d epsilon ≤ n) :
    ∀ n, QuantumTestable d n P epsilon → f d epsilon ≤ n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
