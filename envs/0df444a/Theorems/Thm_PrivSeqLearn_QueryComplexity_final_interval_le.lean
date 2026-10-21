-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_final_interval_le
-- name    : PrivSeqLearn.QueryComplexity.final_interval_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:23.133012+00:00
-- url     : https://prove2.me/theorems/6c8e26f9-931f-43e1-b778-81ec559cad72
-- title:
--   §7.1, p. 19 (footnote 3) — for an accurate strategy the learner's final interval H = [q^i, q^{i+1}) has length at most ϵ
-- statement:
--   Let $\phi$ be a learner strategy of length $N$ that satisfies the accuracy constraint with accuracy $\epsilon$. Fix a true value $x \in [0,1)$ and a seed $y$, let $\bar q = \bar q(x,y)$, and augment it with $q_0 = 0$ and $q_{N+1} = 1$. If $a < b$ are consecutive points of the sorted sequence $(q_0, q_1, \dots, q_N, q_{N+1})$ with $a \le x < b$, then
--   $$b - a \le \epsilon.$$
--
--   Every point of $H = [a,b)$ produces the same responses as $x$, hence the same estimate, so accuracy forces $H$ to be short. This is the source of the special intervals of the lower bound.
--
--   **Formalization Note** "Consecutive" means that no query point lies strictly between $a$ and $b$. Membership in $\Phi_N$ (range $[0,1)$, distinct queries) is not assumed; the statement holds for every accurate strategy.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 19, §7.1 (with footnote 3)

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_SpecialIntervals

namespace PrivSeqLearn.QueryComplexity

/-- The learner's final interval has length at most `ϵ` (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, §7.1, p. 19, with footnote 3):
for an accurate strategy, a true value `x ∈ [0, 1)` and a seed `y`, if `a ≤ x < b` where `a < b` are
consecutive points of the sorted sequence `(0, q_1, …, q_N, 1)` of queries `q = q(x, y)`, then
`b − a ≤ ϵ`.

**Formalization Note** "Consecutive" is encoded as: `a, b` are query points (with `q_0 = 0`,
`q_{N+1} = 1`) and no query point lies strictly between them. Membership in `Φ_N` is not assumed. -/
theorem final_interval_le {N : ℕ} (ϵ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (y : Fin φ.Ybar) (a b : ℝ)
    (ha : a ∈ queryPoints (queries φ x y)) (hb : b ∈ queryPoints (queries φ x y))
    (hax : a ≤ x) (hxb : x < b)
    (hcons : ∀ w ∈ queryPoints (queries φ x y), w ≤ a ∨ b ≤ w) :
    b - a ≤ ϵ := by sorry

end PrivSeqLearn.QueryComplexity
