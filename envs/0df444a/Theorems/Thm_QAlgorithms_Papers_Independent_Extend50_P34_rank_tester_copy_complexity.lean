-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_rank_tester_copy_complexity
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.rank_tester_copy_complexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:18:59.693109+00:00
-- url     : https://prove2.me/theorems/dfcc8dff-1fac-4562-a727-0bf5dcdaa238
-- title:
--   Lemma 6.2
-- statement:
--   For $r\ge1$ and $0<\epsilon\le1/2$, the Rank Tester has copy complexity
--
--   $$\Theta(r^2/\epsilon).$$
--
--   Its upper bound is uniform in every positive ambient dimension and has perfect completeness and soundness error at most $1/3$. Conversely, for some ambient dimension $d>r$, every copy count below an absolute multiple of $r^2/\epsilon$ has an $\epsilon$-far input accepted with probability greater than $1/3$. This establishes both directions for the named tester.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 56, Lemma 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 6.2, arXiv:1501.05028v1, PDF p.56. Correct p.58 non-heavy substring expectation from 2epsilon*d to 2epsilon*n, and its final dimension threshold to the copy count n. Lower bound is existential in d; r=1 uses p.5. -/
theorem rank_tester_copy_complexity
    : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 1 ≤ r →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/2 →
        (∀ d : ℕ, 0 < d → ∃ n : ℕ, (n : ℝ) ≤ C*r^2/epsilon ∧
          RankTesterWorks d n r epsilon) ∧
        (∃ d : ℕ, r < d ∧ ∀ n : ℕ, (n : ℝ) < c*r^2/epsilon →
          ∃ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho ∧
            Far (supportProperty d r) epsilon (decreasingSpectrum rho) ∧ 1/3 < rankAccept n r rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
