-- Prove2me | Theorems.Thm_ProConChoice_Rational_remark_1
-- name    : ProConChoice.Rational.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:26.763815+00:00
-- url     : https://prove2.me/theorems/c27f61a4-f343-4c1f-954a-c28fb1fb811e
-- title:
--   Remark 1, p. 6 — every choice function has a pro-con model in which the chosen alternative is barely chosen and every other one is barely not chosen
-- statement:
--   Let $X$ be a finite set and $C$ a choice function on $X$. Then there is a pro-con model $\langle \succ, \rhd\rangle$ (two disjoint sets of orderings of $X$) such that for every choice set $S$ and every $x \in S$,
--   $$|\mathrm{Pros}(x, S)| - |\mathrm{Cons}(x, S)| = \begin{cases} 1 & \text{if } x = C(S),\\ 0 & \text{otherwise.}\end{cases}$$
--   The chosen alternative is "barely chosen" and every other alternative is "barely not chosen".
--
--   Remark 1 strengthens Theorem 1: such a model is in particular a pro-con representation of $C$ in the sense of Definition 1.
--
--   **Formalization Note** The model is the structure `ProConModel` of the definition `Model` (finite sets of rank bijections, disjoint). The difference of the two cardinalities is taken in $\mathbb{Z}$.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 6, Remark 1

import Mathlib
import Definitions.Def_ProConChoice_Rational_Model

namespace ProConChoice.Rational

/-- Remark 1 (p. 6): every choice function has a "barely chosen" pro-con representation: a pro-con
model with `|Pros(x, S)| - |Cons(x, S)| = 1` if `x = C(S)` and `= 0` for every other `x ∈ S`. -/
theorem remark_1 {X : Type*} [Fintype X] [DecidableEq X]
    (C : Finset X → X) (hC : IsChoiceFunction C) :
    ∃ M : ProConModel X, ∀ S : Finset X, S.Nonempty → ∀ x ∈ S,
      ((M.pros x S).card : ℤ) - (M.cons x S).card = if C S = x then 1 else 0 := by sorry

end ProConChoice.Rational
