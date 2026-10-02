-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_inessential_iff_sum_singletons
-- name    : TheoryOfGames.CharFun.inessential_iff_sum_singletons
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:00:41.224117+00:00
-- url     : https://prove2.me/theorems/fd7e9461-a495-4759-a7d0-4167cce8aaaa
-- title:
--   (27:B) — Γ is inessential iff Σ v((j)) = 0 and essential iff Σ v((j)) < 0
-- statement:
--   Let $v$ be a characteristic function on the subsets of $I = \{1, \dots, n\}$ (it satisfies (25:3:a)–(25:3:c)). Then the game is inessential (its reduced form is $\equiv 0$) if and only if
--   $$\sum_{j=1}^n v((j)) = 0,$$
--   and it is essential (its reduced form is not $\equiv 0$) if and only if
--   $$\sum_{j=1}^n v((j)) < 0 .$$
--
--   This gives an explicit test for essentiality in terms of the values of the one-element coalitions; by (27:8) the two cases are $\gamma = 0$ and $\gamma > 0$.
--
--   **Formalization Note** Players are `Fin n`; "inessential" and "essential" are the definitions `IsInessential`/`IsEssential` through the explicit reduced form (27:2), (27:4).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 250, 27.4.1, (27:B)

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.CharFun

/-- (27:B): a game with characteristic function `v` is inessential if and only if
`∑_{j=1}^n v((j)) = 0`, and it is essential if and only if `∑_{j=1}^n v((j)) < 0`. -/
theorem inessential_iff_sum_singletons {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) :
    (IsInessential v ↔ ∑ j : Fin n, v {j} = 0) ∧
      (IsEssential v ↔ ∑ j : Fin n, v {j} < 0) := by sorry

end TheoryOfGames.CharFun
