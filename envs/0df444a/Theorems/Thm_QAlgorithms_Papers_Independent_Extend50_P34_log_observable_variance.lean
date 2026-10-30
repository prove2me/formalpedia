-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_log_observable_variance
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.log_observable_variance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:15:47.207204+00:00
-- url     : https://prove2.me/theorems/bfdd2520-5f60-4d43-935b-e421173c23d1
-- title:
--   Theorem 5.12
-- statement:
--   In the standing rank-adjacency regime, put $C=\lceil3\log(10r)/\log(\omega/10)\rceil$ and $L_C=\sum_{k=2}^C(-1)^kp_k^*/(kr^k)$. For an absolute $b>0$,
--
--   $$\operatorname{Var}_{\lambda\sim\mathrm{SW}_r^n}L_C(\lambda)\le\exp(bC^{2.01})/\omega^4.$$
--
--   Variance is centered at the actual expectation. This concentration bound is used to strengthen the adjacent-rank TV estimate.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 52, Theorem 5.12

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 5.12, arXiv:1501.05028v1, PDF p.52. Denominator omega⁴; centered variance, not an uncentered second moment. -/
theorem log_observable_variance
    : ∃ b : ℝ, 0 < b ∧ ∀ r n : ℕ, ∀ omega : ℝ,
      RankRegime r n omega →
        schurVariance (n := n) (unif r) (logObservable r (truncation r omega)) ≤
          Real.exp (b*Real.rpow (truncation r omega) (201/100 : ℝ))/omega^4 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
