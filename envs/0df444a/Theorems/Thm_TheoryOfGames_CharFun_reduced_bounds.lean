-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_reduced_bounds
-- name    : TheoryOfGames.CharFun.reduced_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T03:58:50.172057+00:00
-- url     : https://prove2.me/theorems/2b297c1a-d2d9-42a3-a81f-afab574697c2
-- title:
--   (27:7), (27:7*), (27:7**) — −pγ ≦ v̄(S) ≦ (n − p)γ for a reduced characteristic function
-- statement:
--   Let $\bar v$ be a reduced characteristic function on the subsets of $I = \{1, \dots, n\}$ (it satisfies (25:3:a)–(25:3:c) and (27:3)), and let $\gamma$ be defined by (27:5), $-\gamma = \bar v((1)) = \cdots = \bar v((n))$. Then for every $p$-element set $S \subseteq I$:
--
--   $$-p\gamma \leqq \bar v(S) \leqq (n - p)\gamma. \tag{27:7}$$
--
--   Moreover (27:7*): for $p = 0, 1$ the first relation is an equality, $\bar v(S) = -p\gamma$; and (27:7**): for $p = n-1, n$ the second relation is an equality, $\bar v(S) = (n-p)\gamma$.
--
--   These inequalities locate every coalition's value of a reduced game between the value of isolated players and that of the largest coalitions, and underlie the distinction between inessential ($\gamma = 0$) and essential ($\gamma > 0$) games.
--
--   **Formalization Note** Players are `Fin n`; $p$ is `S.card`; $n - p$ is computed in $\mathbb R$. The case $p \geqq n - 1$ is written `n ≤ S.card + 1` to avoid natural-number subtraction.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 248–249, 27.2, (27:5), (27:7), (27:7*), (27:7**)

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.CharFun

/-- (27:7), (27:7*), (27:7**): let `v̄` be a reduced characteristic function and `γ` the number
with (27:5) `-γ = v̄((1)) = ⋯ = v̄((n))`. Then for every `p`-element set `S`
`-pγ ≤ v̄(S) ≤ (n - p)γ`; for `p = 0, 1` the first relation is an equality, and for
`p = n - 1, n` the second relation is an equality. -/
theorem reduced_bounds {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hred : IsReduced v) (γ : ℝ) (hγ : ∀ k : Fin n, v {k} = -γ) :
    (∀ S : Finset (Fin n),
        -((S.card : ℝ) * γ) ≤ v S ∧ v S ≤ ((n : ℝ) - S.card) * γ) ∧
      (∀ S : Finset (Fin n), S.card ≤ 1 → v S = -((S.card : ℝ) * γ)) ∧
      (∀ S : Finset (Fin n), n ≤ S.card + 1 → v S = ((n : ℝ) - S.card) * γ) := by sorry

end TheoryOfGames.CharFun
