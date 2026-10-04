-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_determined_of_subgames
-- name    : TheoryOfGames.PerfectInfo.determined_of_subgames
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T02:53:37.934916+00:00
-- url     : https://prove2.me/theorems/7c9b5e65-33db-4cbf-a691-06809ea83ffa
-- title:
--   (15:C:b) — if every $\Gamma_{\sigma_1}$ is strictly determined, so is $\Gamma$
-- statement:
--   Let $\Gamma$ be a game tree, and let $\Gamma_{\sigma_1}$ ($\sigma_1 = 1, \dots, \alpha_1$) be the games that remain after its first move $\mathfrak M_1$. If every $\Gamma_{\sigma_1}$ is strictly determined, i.e. $v_{\sigma_1/1} = v_{\sigma_1/2}$ for all $\sigma_1$, then $\Gamma$ is strictly determined:
--   $$v_1 = v_2 .$$
--
--   This is the inductive step (15:C:b) of 15.6.1: a game of length $\nu$ has subgames $\Gamma_{\sigma_1}$ of length $\nu - 1$, which are strictly determined by the induction hypothesis.
--
--   **Formalization Note** The statement is made for every tree; for a game of length $0$ there are no $\Gamma_{\sigma_1}$ and the conclusion is (15:C:a).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 123, 15.6.1, (15:C:b) and its proof

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

namespace TheoryOfGames.PerfectInfo

open GameTree

/-- (15:C:b), inductive step: if every game `Γ_{σ₁}` that remains after the first move of `Γ` is
strictly determined, then `Γ` is strictly determined. -/
theorem determined_of_subgames (t : GameTree)
    (h : ∀ s ∈ t.firstMoveSubgames, IsStrictlyDetermined s) :
    IsStrictlyDetermined t := by sorry

end TheoryOfGames.PerfectInfo
