-- Prove2me | Theorems.Thm_ProConChoice_Rational_theorem_1
-- name    : ProConChoice.Rational.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:42.713295+00:00
-- url     : https://prove2.me/theorems/c2cd533a-a352-4900-83c8-670d09214cd1
-- title:
--   Theorem 1, p. 6 — every choice function is pro-con rational
-- statement:
--   Let $X$ be a finite set of alternatives and $C$ a choice function on $X$, assigning to every nonempty $S \subseteq X$ an alternative $C(S) \in S$. Then $C$ is pro-con rational: there are two disjoint sets of orderings of $X$, the pro-orderings $\succ$ and the con-orderings $\rhd$, such that for every choice set $S$ and every $x \in S$,
--   $$C(S) = x \iff |\mathrm{Pros}(x, S)| > |\mathrm{Cons}(x, S)|,$$
--   where $\mathrm{Pros}(x, S)$ ($\mathrm{Cons}(x, S)$) is the set of pro-orderings (con-orderings) whose top-ranked alternative in $S$ is $x$.
--
--   The theorem says that the pro-con model, in which an alternative is chosen when the orderings that rank it first among the available alternatives as a reason for choosing it outnumber those that rank it first as a reason against, imposes no restriction on choice behaviour: every choice function, however inconsistent, has such a representation.
--
--   **Formalization Note** Orderings are rank bijections and the pro and con sets are disjoint `Finset`s of them (definition `Model`), so no ordering is used twice; the equivalence must hold at every alternative of every nonempty choice set, with one model for all choice sets.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 6, Theorem 1 (proof in Section 7, pp. 22–23)

import Mathlib
import Definitions.Def_ProConChoice_Rational_Model

namespace ProConChoice.Rational

/-- Theorem 1 (p. 6): every choice function is pro-con rational. -/
theorem theorem_1 {X : Type*} [Fintype X] [DecidableEq X]
    (C : Finset X → X) (hC : IsChoiceFunction C) : ProConRational C := by sorry

end ProConChoice.Rational
