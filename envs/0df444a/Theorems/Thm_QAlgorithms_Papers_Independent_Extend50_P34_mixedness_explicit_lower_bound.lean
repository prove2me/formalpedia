-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_mixedness_explicit_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.mixedness_explicit_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:59:37.82167+00:00
-- url     : https://prove2.me/theorems/5ec8b5f0-55eb-4fea-ab5f-05159df01403
-- title:
--   Corollary 4.3
-- statement:
--   For every even positive dimension $d$ and $0<\epsilon\le1/2$, any collective $\epsilon$-tester for the maximally mixed state with success probability at least $2/3$ must use
--
--   $$n\ge0.15\,d/\epsilon^2.$$
--
--   The lower bound applies to all testers fixed before the unknown input state, not only to the Mixedness Tester.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 34, Corollary 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Corollary 4.3, arXiv:1501.05028v1, PDF p.34. The perturbation proof requires epsilon≤1/2, and the numerical constant .15 is retained. -/
theorem mixedness_explicit_lower_bound
    (d n : ℕ) (hd : 0 < d) (heven : Even d)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1/2)
    (hTest : QuantumTestable d n {unif d} epsilon) :
    (15/100 : ℝ)*d/epsilon^2 ≤ n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
