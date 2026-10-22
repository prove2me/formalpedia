-- Prove2me | Theorems.Thm_TBSGStrategyIteration_valueIterOp_contraction
-- name    : TBSGStrategyIteration.valueIterOp_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:05:44.029189+00:00
-- url     : https://prove2.me/theorems/473fa9d4-4a89-4c39-942c-ba9ed3d64006
-- title:
--   Lemma 4.2 — the value iteration operator is a $\gamma$-contraction
-- statement:
--   For all $u, v \in \mathbb{R}^n$,
--   $$\|\mathcal T u - \mathcal T v\|_\infty \le \gamma \, \|u - v\|_\infty ,$$
--   where $\mathcal T$ is the min/max value iteration operator of the two-player game.
--
--   **Formalization Note.** `‖·‖` on `S → ℝ` is Mathlib's sup norm $\|x\|_\infty = \max_i |x_i|$ (and $0$ when $S$ is empty).
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 6, Lemma 4.2

import Mathlib
import Definitions.Def_TBSGStrategyIteration_valueIterOp

namespace TBSGStrategyIteration

/-- Lemma 4.2: the value iteration operator is a `γ`-contraction in the sup norm:
`‖𝒯u − 𝒯v‖_∞ ≤ γ ‖u − v‖_∞` for all `u, v ∈ ℝ^n`. (The norm on `S → ℝ` is Mathlib's sup norm.) -/
theorem valueIterOp_contraction {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (u v : S → ℝ) :
    ‖valueIterOp G u - valueIterOp G v‖ ≤ G.γ * ‖u - v‖ := by sorry

end TBSGStrategyIteration
