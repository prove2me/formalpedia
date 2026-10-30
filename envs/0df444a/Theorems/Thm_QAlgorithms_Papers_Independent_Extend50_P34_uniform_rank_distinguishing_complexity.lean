-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_uniform_rank_distinguishing_complexity
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.uniform_rank_distinguishing_complexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:42:24.887068+00:00
-- url     : https://prove2.me/theorems/0c5d0722-eb72-4405-8c7b-6fb9765199cf
-- title:
--   Theorem 1.12
-- statement:
--   For integers $1\le\Delta\le r$, uniform spectra on $r$ and $r+\Delta$ eigenvalues can be distinguished with $O(r^2/\Delta)$ copies. Conversely, for some absolute $b,c>0$ and all sufficiently large $r$, every such tester uses
--
--   $$n\ge\frac{c}{\Delta}\,r^{\,2-b/(\log r)^{0.33}}.$$
--
--   Both bounds hold uniformly in every ambient dimension $d\ge r+\Delta$ and every eigenbasis, with success probability $2/3$. The displayed lower bound is the precise meaning of the source's nearly quadratic notation (equation (27)).
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 1, Theorem 1.12

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 1.12, arXiv:1501.05028v1, PDF p.1. Use equation (27), not division by a polylogarithm. Constants and r-threshold precede Delta,d and the input state. -/
theorem uniform_rank_distinguishing_complexity
    : (∃ A : ℝ, 0 < A ∧ ∀ r Delta : ℕ, 1 ≤ Delta → Delta ≤ r →
        ∀ d : ℕ, r+Delta ≤ d → ∃ n : ℕ, (n : ℝ) ≤ A*r^2/Delta ∧
          DistinguishesRanks d n r Delta) ∧
      (∃ b c : ℝ, 0 < b ∧ 0 < c ∧ ∃ r0 : ℕ, 2 ≤ r0 ∧
        ∀ r : ℕ, r0 ≤ r → ∀ Delta : ℕ, 1 ≤ Delta → Delta ≤ r →
          ∀ d : ℕ, r+Delta ≤ d → ∀ n : ℕ,
            DistinguishesRanks d n r Delta →
              c * Real.rpow r (2 - b / Real.rpow (Real.log r) (33/100 : ℝ)) / Delta ≤ n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
