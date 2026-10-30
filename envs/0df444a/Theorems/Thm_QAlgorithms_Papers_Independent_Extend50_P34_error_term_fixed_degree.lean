-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_error_term_fixed_degree
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.error_term_fixed_degree
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:12:10.085267+00:00
-- url     : https://prove2.me/theorems/a81fcded-1719-43cc-9555-ef0b2825bf13
-- title:
--   Lemma 5.7
-- statement:
--   For every fixed integer $C\ge2$, there is $A_C\ge0$, independent of $r,n,\omega$, such that throughout $n=r^2/\omega^2$, $200\le\omega\le\sqrt r$,
--
--   $$\left|\sum_{k=2}^C\frac{(-1)^k\mathbb E_{\mathrm{SW}_r^n}O_k}{kr^k}\right|\le A_C/\omega^2.$$
--
--   Here $O_k$ is the computed remainder in Proposition 5.5. This bounds the whole error term (39), rather than each remainder pointwise.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 50, Lemma 5.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 5.7, arXiv:1501.05028v1, PDF p.50.  -/
theorem error_term_fixed_degree
    (C : ℕ) (hC : 2 ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r n : ℕ, ∀ omega : ℝ,
      RankRegime r n omega → |errorTerm r n C| ≤ A/omega^2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
