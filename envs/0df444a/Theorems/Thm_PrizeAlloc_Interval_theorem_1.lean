-- Prove2me | Theorems.Thm_PrizeAlloc_Interval_theorem_1
-- name    : PrizeAlloc.Interval.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:45.220981+00:00
-- url     : https://prove2.me/theorems/368419bb-a76b-44d6-888e-5f5148f2e179
-- title:
--   Theorem 1 — a prize allocation rule satisfies order preservation, endowment monotonicity and consistency iff it is an interval rule
-- statement:
--   Let $U$ be a countable set of at least three potential competitors and $\varphi$ a prize allocation rule on the competitions over $U$. Then
--   $$\varphi \text{ satisfies order preservation, endowment monotonicity and consistency} \iff \varphi \text{ is an interval rule.}$$
--
--   The theorem describes every rule that rewards rank weakly, never takes prize money away when the endowment grows, and allocates coherently across subgroups: there are disjoint intervals $(a_k, b_k)$ on which prizes are raised from $a_k$ to $b_k$ one competitor at a time from the top, and equal division elsewhere. Equal Division, Winner-Takes-All and the rule of Example 1 are special cases; Corollaries 1–4 single out ED, WTA and the Winner-Takes-Surplus rules inside this family.
--
--   **Formalization Note** The standing assumption that $U$ is countable with at least three elements (p. 8) is carried as `[Countable U]` and three distinct elements. Competitions range over all nonempty finite rankings of elements of $U$ and all endowments $E \ge 0$; anonymity is not assumed (Lemma 2 derives it). Interval rules allow $b_k = +\infty$ (extended reals).
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 13, Theorem 1 (proof pp. 27–30)

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Interval

theorem theorem_1 {U : Type*} [DecidableEq U] [Countable U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ) :
    (OrderPreserving φ ∧ EndowmentMonotone φ ∧ Consistent φ) ↔ IsIntervalRule φ := by sorry

end PrizeAlloc.Interval
