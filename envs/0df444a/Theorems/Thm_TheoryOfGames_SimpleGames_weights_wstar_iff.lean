-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_weights_wstar_iff
-- name    : TheoryOfGames.SimpleGames.weights_wstar_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:02:17.22765+00:00
-- url     : https://prove2.me/theorems/cb7b9bca-bcfa-4080-b6d2-bbff980f1f9c
-- title:
--   (50:B) — non-negative weights define a W with (49:W*) iff they fulfil (50:B:a), (50:B:b)
-- statement:
--   Let $w_1, \dots, w_n \geqq 0$ be non-negative weights and let $W$ be the set of all $S \subseteq I$ with $\sum_{i \in S} w_i > \tfrac12 \sum_{i=1}^n w_i$ (50:1). Then $W$ satisfies (49:W*) if and only if
--
--   1. (50:B:a) $0 \leqq w_{i_0} < \tfrac12 \sum_{i=1}^n w_i$ for all $i_0 = 1, \dots, n$, and
--   2. (50:B:b) $\sum_{i \in S} w_i \neq \tfrac12 \sum_{i=1}^n w_i$ for all $S \subseteq I$.
--
--   Verbally: no player has half the total weight or more, and no combination of players has precisely half. The weights satisfying (50:B) are exactly those defining a simple game, the weighted majority game $[w_1, \dots, w_n]$.
--
--   **Formalization Note** The book states the equivalence for arbitrary real weights. Its argument for (49:W*:b) uses $w_i \geqq 0$ ("clearly satisfied if all $w_i \geqq 0$"), and without that assumption the "only if" direction is false: $[10, 10, 10, -\tfrac1{10}]$ defines the $W$ of the direct majority of the first three players, which satisfies (49:W*), while $w_4 < 0$. The statement is therefore made for non-negative weights, where it is exactly the book's equivalence; the "if" direction is unaffected, since (50:B:a) contains $w_i \geqq 0$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 433, (50:B); p. 429, (49:W*)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

namespace TheoryOfGames.SimpleGames

/-- (50:B), p. 433, for non-negative weights: the weights `w₁, …, wₙ` define by (50:1) a `W`
which satisfies (49:W*) if and only if they fulfil (50:B:a) and (50:B:b).
(The book states the equivalence without the standing assumption `wᵢ ≧ 0`; its sufficiency
argument for (49:W*:b) uses `wᵢ ≧ 0`, and without it the "only if" fails — e.g.
`[10, 10, 10, -1/10]` defines the `W` of the direct majority of the first three players.) -/
theorem weights_wstar_iff {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    SatisfiesWStar (weightedW w) ↔ SatisfiesB w := by sorry

end TheoryOfGames.SimpleGames
