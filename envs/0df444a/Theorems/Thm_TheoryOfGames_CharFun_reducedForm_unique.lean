-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_reducedForm_unique
-- name    : TheoryOfGames.CharFun.reducedForm_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:55:59.018988+00:00
-- url     : https://prove2.me/theorems/89e420f8-24be-4fcc-b361-f284080087c7
-- title:
--   (27:A) — every characteristic function is strategically equivalent to precisely one reduced one
-- statement:
--   Let $v$ be a characteristic function on the subsets of $I = \{1, \dots, n\}$, i.e. a set function satisfying (25:3:a)–(25:3:c). Let $\bar v$ be its reduced form, given by (27:2) and (27:4):
--   $$\bar v(S) = v(S) + \sum_{k \in S} \alpha^0_k, \qquad \alpha^0_k = -v((k)) + \frac1n \sum_{j=1}^n v((j)).$$
--   Then for every set function $w$ the following are equivalent:
--
--   1. $w$ is a characteristic function, $w$ is reduced ($w((1)) = \cdots = w((n))$), and $w$ is strategically equivalent to $v$;
--   2. $w = \bar v$.
--
--   In words: every characteristic function is in strategic equivalence with precisely one reduced characteristic function, and it is given by the formulae (27:2), (27:4). The reduced form is the representative of its class of strategically equivalent games used throughout the rest of the theory.
--
--   **Formalization Note** Players are `Fin n`, coalitions `Finset (Fin n)`; strategic equivalence requires $\sum_k \alpha^0_k = 0$, (27:1).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 248, (27:A), with (27:2)–(27:4), pp. 246–248

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.CharFun

/-- (27:A): every characteristic function `v(S)` is in strategic equivalence with precisely one
reduced characteristic function `v̄(S)`, and this `v̄(S)` is given by the formulae (27:2) and
(27:4) (`reducedForm v`): a set function `w` is a reduced characteristic function strategically
equivalent to `v` if and only if `w = reducedForm v`. -/
theorem reducedForm_unique {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (w : Finset (Fin n) → ℝ) :
    (IsCharFunction w ∧ IsReduced w ∧ StrategicallyEquivalent v w) ↔ w = reducedForm v := by sorry

end TheoryOfGames.CharFun
