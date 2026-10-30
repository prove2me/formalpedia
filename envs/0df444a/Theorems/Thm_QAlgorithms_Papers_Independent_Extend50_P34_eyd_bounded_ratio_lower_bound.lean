-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_eyd_bounded_ratio_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.eyd_bounded_ratio_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:55:41.018986+00:00
-- url     : https://prove2.me/theorems/9f9fdb25-d83a-4f35-a42c-4145b4799cc2
-- title:
--   Theorem 3.4
-- statement:
--   For every fixed $C>0$, there are $0<\delta,\epsilon<1$ and $d_0\ge2$, depending only on $C$, such that for every $d\ge d_0$ and $1\le n\le Cd^2$,
--
--   $$\Pr_{\lambda\sim\mathrm{SW}_d^n}[d_{\rm TV}(\bar\lambda,\mathrm{Unif}_d)>\epsilon]\ge\delta.$$
--
--   This is uniform over the entire integer range of $n$. It covers the bounded-copy-to-dimension regime needed for the EYD lower bound.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 30, Theorem 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 3.4, arXiv:1501.05028v1, PDF p.30. Use the closed-boundary restatement on PDF p.59; the original p.30 uses n<Cd². Positive n is required. -/
theorem eyd_bounded_ratio_lower_bound
    (C : ℝ) (hC : 0 < C) :
    ∃ delta epsilon : ℝ, 0 < delta ∧ delta < 1 ∧ 0 < epsilon ∧ epsilon < 1 ∧
      ∃ d0 : ℕ, 2 ≤ d0 ∧ ∀ d : ℕ, d0 ≤ d → ∀ n : ℕ, 0 < n →
        (n : ℝ) ≤ C*d^2 →
          delta ≤ event (n := n) (unif d) (fun lambda => epsilon < eydError n (unif d) lambda) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
