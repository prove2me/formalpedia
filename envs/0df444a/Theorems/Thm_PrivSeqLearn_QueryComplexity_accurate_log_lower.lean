-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_accurate_log_lower
-- name    : PrivSeqLearn.QueryComplexity.accurate_log_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:31.375108+00:00
-- url     : https://prove2.me/theorems/0aa326f6-d042-486d-9c23-85a56e930db3
-- title:
--   p. 20 — first term of the lower bound: an accurate strategy of length N has N ≥ log(1/ϵ)
-- statement:
--   Let $\epsilon > 0$ and let $\phi$ be a learner strategy of length $N$ that satisfies the accuracy constraint. Then
--   $$N \ge \left\lceil \log_2 \frac 1\epsilon \right\rceil.$$
--
--   This is the classical bisection lower bound on $[0,1)$, and the first term of the lower bound in Theorem 4.1; it holds without any privacy requirement.
--
--   **Formalization Note** Membership in $\Phi_N$ and privacy are not assumed. The logarithm is base 2 and rounded up (footnote 1, p. 4), computed in the integers.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 20, remark after Lemma 7.1 (first term of the lower bound in Theorem 4.1)

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting

namespace PrivSeqLearn.QueryComplexity

/-- First term of the lower bound in Theorem 4.1 (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 20, after Lemma 7.1): an accurate
learner strategy of length `N` has `N ≥ ⌈log₂(1/ϵ)⌉`.

**Formalization Note** Membership in `Φ_N` and privacy are not assumed; only accuracy and `ϵ > 0`. -/
theorem accurate_log_lower {N : ℕ} (ϵ : ℝ) (φ : Strategy N) (hϵ : 0 < ϵ)
    (hacc : IsAccurate ϵ φ) :
    ⌈Real.logb 2 (1 / ϵ)⌉ ≤ (N : ℤ) := by sorry

end PrivSeqLearn.QueryComplexity
