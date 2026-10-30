-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_eyd_large_ratio_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.eyd_large_ratio_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:56:21.99374+00:00
-- url     : https://prove2.me/theorems/8326161e-ab40-4962-92f2-37d94161a6f5
-- title:
--   Theorem 3.5
-- statement:
--   There are absolute $C,a>0$ and $0<\delta<1$ such that for $d\ge2$, $n\ge Cd^2$, and $\epsilon>0$ with $n<a d^2/\epsilon^2$,
--
--   $$\Pr_{\lambda\sim\mathrm{SW}_d^n}[d_{\rm TV}(\bar\lambda,\mathrm{Unif}_d)>\epsilon]\ge\delta.$$
--
--   The source proof permits $C=10^{10}$ and $\delta=0.01$, with error at least $d/(400000\sqrt n)$. This supplies the large-$n$ part of the EYD lower bound.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 30, Theorem 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 3.5, arXiv:1501.05028v1, PDF p.30. Exclude d=1; the source proof retains absolute deviations, whose bars are lost in extraction. -/
theorem eyd_large_ratio_lower_bound
    : ∃ C a delta : ℝ, 0 < C ∧ 0 < a ∧ 0 < delta ∧ delta < 1 ∧
      ∀ d : ℕ, 2 ≤ d → ∀ n : ℕ, 0 < n → C*d^2 ≤ (n : ℝ) →
        ∀ epsilon : ℝ, 0 < epsilon → (n : ℝ) < a*d^2/epsilon^2 →
          delta ≤ event (n := n) (unif d) (fun lambda => epsilon < eydError n (unif d) lambda) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
