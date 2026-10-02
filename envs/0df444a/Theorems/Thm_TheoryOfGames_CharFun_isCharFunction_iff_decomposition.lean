-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_isCharFunction_iff_decomposition
-- name    : TheoryOfGames.CharFun.isCharFunction_iff_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:49:01.169592+00:00
-- url     : https://prove2.me/theorems/46cd6162-d19a-4a3f-b3e4-5029e6cb45f2
-- title:
--   (25:A) — (25:3:a)–(25:3:c) are equivalent to (25:6) for p = 1, 2, 3
-- statement:
--   Let $v$ be a numerical set function on the subsets of $I = \{1, \dots, n\}$. A decomposition of $I$ is a system $S_1, \dots, S_p$ of pairwise disjoint subsets of $I$ with the sum $I$ (members may be empty). Then $v$ satisfies (25:3:a)–(25:3:c) if and only if all three of the following hold:
--
--   1. ($p = 1$) $v(S_1) = 0$ for the decomposition $S_1 = I$;
--   2. ($p = 2$) $v(S_1) + v(S_2) = 0$ for every decomposition $S_1, S_2$ of $I$;
--   3. ($p = 3$) $v(S_1) + v(S_2) + v(S_3) \leqq 0$ for every decomposition $S_1, S_2, S_3$ of $I$.
--
--   $$v(S_1) + \cdots + v(S_p) \ \begin{cases} = 0 & p = 1, 2,\\ \leqq 0 & p = 3,\end{cases} \qquad S_1, \dots, S_p \text{ a decomposition of } I.$$
--
--   These are the cases $p = 1, 2, 3$ of (25:6), sharpened to equalities for $p = 1, 2$; the result says that the conditions on a characteristic function can be checked on decompositions of $I$ into at most three parts.
--
--   **Formalization Note** Coalitions are `Finset (Fin n)`; "pairwise disjoint with sum $I$" is written as pairwise `Disjoint` together with the union being `Finset.univ`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 242, 25.4.2, (25:A), with (25:6)

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

namespace TheoryOfGames.CharFun

/-- (25:A): the conditions (25:3:a)–(25:3:c) are equivalent to (25:6) for `p = 1, 2, 3` only,
stated with `=` for `p = 1, 2` and with `≤` for `p = 3`. A decomposition of `I` is a system of
pairwise disjoint subsets of `I` with the sum `I` (empty members allowed, as in 25.3.1). -/
theorem isCharFunction_iff_decomposition {n : ℕ} (v : Finset (Fin n) → ℝ) :
    IsCharFunction v ↔
      ((∀ S₁ : Finset (Fin n), S₁ = Finset.univ → v S₁ = 0) ∧
        (∀ S₁ S₂ : Finset (Fin n), Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
          v S₁ + v S₂ = 0) ∧
        (∀ S₁ S₂ S₃ : Finset (Fin n), Disjoint S₁ S₂ → Disjoint S₁ S₃ → Disjoint S₂ S₃ →
          S₁ ∪ S₂ ∪ S₃ = Finset.univ → v S₁ + v S₂ + v S₃ ≤ 0)) := by sorry

end TheoryOfGames.CharFun
