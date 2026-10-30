-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_rank_copy_complexity
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.rank_copy_complexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:41:41.229305+00:00
-- url     : https://prove2.me/theorems/9dfc3c66-1a3e-4701-a5fd-66beb853f26b
-- title:
--   Theorem 1.11
-- statement:
--   For $r\ge1$ and $0<\epsilon\le1/2$, rank at most $r$ can be tested with perfect completeness using $O(r^2/\epsilon)$ iid copies, uniformly in the ambient dimension. In sufficiently large ambient dimension, every such tester needs $\Omega(r^2/\epsilon)$ copies, while every two-sided tester needs $\Omega(r/\epsilon)$ copies:
--
--   $$n_{\text{one-sided}}=\Theta(r^2/\epsilon),\qquad n_{\text{two-sided}}=\Omega(r/\epsilon).$$
--
--   Soundness is rejection with probability at least $2/3$ for every state $\epsilon$-far from rank at most $r$. The lower bounds are worst case in the ambient dimension.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 1, Theorem 1.11

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 1.11, arXiv:1501.05028v1, PDF p.1. At most r; upper uniform in d, lower existential in d. r=1 uses pure-state testing (p.5); the section 6.2 construction needs r≥2. -/
theorem rank_copy_complexity
    : ∃ C c b : ℝ, 0 < C ∧ 0 < c ∧ 0 < b ∧
      ∀ r : ℕ, 1 ≤ r → ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/2 →
        (∀ d : ℕ, 0 < d → ∃ n : ℕ, (n : ℝ) ≤ C * r^2 / epsilon ∧
          QuantumTestable d n (supportProperty d r) epsilon true) ∧
        (∃ d : ℕ, r < d ∧ ∀ n : ℕ,
          QuantumTestable d n (supportProperty d r) epsilon true →
          c * r^2 / epsilon ≤ n) ∧
        (∃ d : ℕ, r < d ∧ ∀ n : ℕ,
          QuantumTestable d n (supportProperty d r) epsilon false →
          b * r / epsilon ≤ n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
