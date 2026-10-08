-- Prove2me | Theorems.Thm_ThomsonKS_Char_corollary_1
-- name    : ThomsonKS.Char.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:47.776002+00:00
-- url     : https://prove2.me/theorems/0ae5515b-2da6-400b-918f-a7df62c319ca
-- title:
--   Corollary 1, p. 322 — under WPO, An, S. Inv and Mon, F coincides with K on Σ̃^P
-- statement:
--   Let $F$ be a solution: for every finite group $P$ of agents and every $S \in \Sigma^P$ it selects a point $F^P(S) \in S$. If $F$ satisfies WPO, An, S. Inv and Mon, then
--
--   $$F^P(S) = K^P(S) \qquad \text{for every finite group } P \text{ and every } S \in \tilde\Sigma^P,$$
--
--   where $\tilde\Sigma^P$ is the class of problems in $\Sigma^P$ satisfying (c): for all $x, y \in S$ with $y \geqslant x$ ($y \geqq x$, $y \ne x$) there is $z \in S$ with $z > x$ in every coordinate. On such problems weakly Pareto-optimal points are Pareto-optimal.
--
--   Continuity is not needed on this restricted class; it enters only to pass from $\tilde\Sigma^P$ to all of $\Sigma^P$ (Theorem 3).
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), p. 322, Corollary 1 (condition (c) on the same page)

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

namespace ThomsonKS.Char

theorem corollary_1 (F : Solution) (hF : IsSolution F) (hW : WPO F) (hA : An F)
    (hI : SInv F) (hM : Mon F) : ∀ P : Finset ℕ, ∀ S ∈ DivProbTilde P, F P S = KS P S := by sorry

end ThomsonKS.Char
