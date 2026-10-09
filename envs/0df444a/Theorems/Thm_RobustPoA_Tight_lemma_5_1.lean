-- Prove2me | Theorems.Thm_RobustPoA_Tight_lemma_5_1
-- name    : RobustPoA.Tight.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:55.203566+00:00
-- url     : https://prove2.me/theorems/9861902c-003c-4a8d-b8c4-0ddd2ab59192
-- title:
--   Lemma 5.1, p. 23 — nonnegativity of μ
-- statement:
--   Let $\mathcal C$ be a nonempty set of nonnegative, nondecreasing, strictly positive cost functions. For every $(\lambda,\mu)\in\mathcal A(\mathcal C)$,
--
--   $$\mu\ge0.$$
--
--   The lemma fixes the sign of the second smoothness parameter under strict positivity, as used when resourcewise bounds are summed across a game.
--
--   **Formalization Note** Admissibility includes nondecreasing costs at positive loads; the all-zero function is excluded by the standing convention of §5.1.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Lemma 5.1, p. 23

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

/-- Lemma 5.1, p. 23: an admissible smoothness pair for nonempty, strictly positive
cost functions has nonnegative second coordinate. -/
theorem lemma_5_1 (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c ∧ IsStrictlyPos c)
    (p : ℝ × ℝ) (hp : p ∈ smoothParams C) : 0 ≤ p.2 := by sorry

end RobustPoA.Tight
