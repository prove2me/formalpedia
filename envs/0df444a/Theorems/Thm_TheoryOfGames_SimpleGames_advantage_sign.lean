-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_advantage_sign
-- name    : TheoryOfGames.SimpleGames.advantage_sign
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:05:03.323462+00:00
-- url     : https://prove2.me/theorems/c5e261a5-8075-4f9d-a953-7ea8e7a03dd5
-- title:
--   (50:D) — a_S > 0 iff S ∈ W, a_S < 0 iff S ∈ L, a_S = 0 is impossible
-- statement:
--   Let $w_1, \dots, w_n$ fulfil (50:B), let $W$ be given by (50:1), and let $L$ be the set of losing coalitions of the weighted majority game, i.e. of the complements $-S$ of the elements $S$ of $W$ (48:A:b). For every $S \subseteq I$ let $a_S = 2\sum_{i \in S} w_i - \sum_{i=1}^n w_i$ (50:6). Then
--
--   1. (50:D:a) $a_S > 0$ if and only if $S$ belongs to $W$;
--   2. (50:D:b) $a_S < 0$ if and only if $S$ belongs to $L$;
--   3. (50:D:c) $a_S = 0$ is impossible.
--
--   The sign of $a_S$ thus decides whether a coalition wins; homogeneity (50:E) asks that its size be the same on the minimal winning coalitions.
--
--   **Formalization Note** "$S$ belongs to $L$" is written $-S \in W$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 434, (50:D), (50:6)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

namespace TheoryOfGames.SimpleGames

/-- (50:D), p. 434: for weights fulfilling (50:B), with `W` given by (50:1) and `L` the set of
complements of the elements of `W` (48:A:b):
(50:D:a) `a_S > 0` if and only if `S` belongs to `W`;
(50:D:b) `a_S < 0` if and only if `S` belongs to `L`;
(50:D:c) `a_S = 0` is impossible. -/
theorem advantage_sign {n : ℕ} (w : Fin n → ℝ) (hB : SatisfiesB w) (S : Finset (Fin n)) :
    (0 < advantage w S ↔ S ∈ weightedW w) ∧
    (advantage w S < 0 ↔ Sᶜ ∈ weightedW w) ∧
    advantage w S ≠ 0 := by sorry

end TheoryOfGames.SimpleGames
