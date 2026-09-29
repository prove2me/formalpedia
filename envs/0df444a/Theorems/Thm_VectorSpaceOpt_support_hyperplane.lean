-- Prove2me | Theorems.Thm_VectorSpaceOpt_support_hyperplane
-- name    : VectorSpaceOpt.support_hyperplane
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:53:39.636601+00:00
-- url     : https://prove2.me/theorems/10c210c0-639f-4721-95d3-5c0f5a2abdbb
-- title:
--   The support theorem
-- statement:
--   Let $K$ be a convex set with nonempty interior in a real normed space $X$, and let $x$ be a point that is **not an interior point** of $K$. Then there is a closed hyperplane through $x$ with $K$ lying on one side of it: a **nonzero** $x^* \in X^*$ with
--
--   $$\langle k, x^*\rangle \le \langle x, x^*\rangle \qquad \text{for all } k \in K.$$
--
--   A closed hyperplane is a **support** for $K$ when $K$ lies in one of the closed half-spaces it determines and the hyperplane meets $K$. The theorem therefore says that a supporting hyperplane can be constructed through any boundary point of a convex set with interior points — the geometric fact that a convex body is "held up" from outside at every point of its boundary.
--
--   It follows immediately from Mazur's theorem applied to the variety $\{x\}$.
--
--   **Formalization Note.** The hypothesis is only $x \notin \operatorname{int} K$; the point may be a boundary point of $K$, may belong to $K$, or may lie far from it. The separating constant is $\langle x, x^*\rangle$ itself, so no separate constant is introduced.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.12, Theorem 2, p. 133

import Mathlib

namespace VectorSpaceOpt

theorem support_hyperplane {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (x : X) (hx : x ∉ interior K) :
    ∃ f : X →L[ℝ] ℝ, f ≠ 0 ∧ ∀ k ∈ K, f k ≤ f x := by sorry

end VectorSpaceOpt
