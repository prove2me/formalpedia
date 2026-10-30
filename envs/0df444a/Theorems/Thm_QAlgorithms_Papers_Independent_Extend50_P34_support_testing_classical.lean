-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_support_testing_classical
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.support_testing_classical
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:38:28.275109+00:00
-- url     : https://prove2.me/theorems/8c031a9a-7173-41a9-ade9-af43b2d9f838
-- title:
--   Theorem 1.5
-- statement:
--   Fix a constant accuracy $0<\epsilon\le1/3$. For testing whether a distribution on an arbitrary finite alphabet has at most $r$ positive probabilities, there are positive constants $C,c$ and a threshold $r_0\ge2$, depending only on $\epsilon$, such that for every $r\ge r_0$,
--
--   $$n_{\rm upper}\le Cr,\qquad n_{\rm lower}\ge c\,r/\log r.$$
--
--   The upper bound is uniform over alphabet sizes. The lower bound holds for some alphabet size larger than $r$. Both bounds use iid samples and worst-input success probability at least $2/3$. This compares classical support testing with quantum rank testing.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 5, Theorem 1.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 1.5, arXiv:1501.05028v1, PDF p.5. Support means at most r. Fixed-accuracy constants precede r and the alphabet; the lower bound is worst case over the alphabet. -/
theorem support_testing_classical
    : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/3 →
      ∃ (C c : ℝ) (r0 : ℕ), 0 < C ∧ 0 < c ∧ 2 ≤ r0 ∧
        ∀ r : ℕ, r0 ≤ r →
          (∀ d : ℕ, 0 < d → ∃ n : ℕ, (n : ℝ) ≤ C * r ∧
            ClassicalTestable d n (supportProperty d r) epsilon) ∧
          (∃ d : ℕ, r < d ∧ ∀ n : ℕ,
            ClassicalTestable d n (supportProperty d r) epsilon →
            c * r / Real.log r ≤ n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
