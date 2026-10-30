-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_eyd_small_accuracy_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.eyd_small_accuracy_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:54:54.611114+00:00
-- url     : https://prove2.me/theorems/0f6d75df-a2fe-40d1-8bde-fb5356bf7f45
-- title:
--   Theorem 3.3
-- statement:
--   There are absolute constants $0<\delta<1$, $\epsilon_0>0$, $a>0$, and $d_0\ge2$ such that for every $d\ge d_0$, $0<\epsilon\le\epsilon_0$, and integer $1\le n<a d^2/\epsilon^2$, the EYD output $\bar\lambda$ for the maximally mixed state satisfies
--
--   $$\Pr_{\lambda\sim\mathrm{SW}_d^n}[d_{\rm TV}(\bar\lambda,\mathrm{Unif}_d)>\epsilon]\ge\delta.$$
--
--   Thus EYD requires $\Omega(d^2/\epsilon^2)$ copies for accurate spectrum estimation at this fixed failure level. This is specific to EYD, not a lower bound for every estimator.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 30, Theorem 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 3.3, arXiv:1501.05028v1, PDF p.30. Theorem 3.3 pins the fixed positive failure probability meant by Theorem 1.13. Positive n excludes division by zero. -/
theorem eyd_small_accuracy_lower_bound
    : EYDLowerBound := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
