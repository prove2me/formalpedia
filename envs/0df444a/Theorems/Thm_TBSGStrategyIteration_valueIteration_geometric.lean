-- Prove2me | Theorems.Thm_TBSGStrategyIteration_valueIteration_geometric
-- name    : TBSGStrategyIteration.valueIteration_geometric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:10:01.283876+00:00
-- url     : https://prove2.me/theorems/a3c4d00b-2f6a-4a45-98a8-a64bddf39093
-- title:
--   Lemma 4.8 — geometric convergence of value iteration
-- statement:
--   Let $\pi^*$ be an optimal strategy profile and $v^* = v_{\pi^*}$ the optimal value vector. For every $u^0 \in \mathbb{R}^n$, the value-iteration iterates $u^k = \mathcal T^k u^0$ satisfy, for every $k \ge 0$,
--   $$\|u^k - v^*\|_\infty \le \gamma^k \, \|u^0 - v^*\|_\infty .$$
--
--   **Formalization Note.** The paper states this for the finite sequence $(u^k)_{k=0}^N$ produced by a call Value-Iteration$(u^0, \varepsilon)$, which is a prefix of the infinite iterate sequence; the Lean statement covers every $k$. $v^*$ is given as the value vector of an optimal profile (unique by Theorem 2.8).
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 7, Lemma 4.8

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal
import Definitions.Def_TBSGStrategyIteration_valueIterOp

namespace TBSGStrategyIteration

/-- Lemma 4.8: the value-iteration iterates `u^k = 𝒯^k u^0` satisfy
`‖u^k − v*‖_∞ ≤ γ^k ‖u^0 − v*‖_∞`, where `v* = v_{π*}` is the optimal value vector (the value
vector of any optimal profile `π*`, unique by Theorem 2.8). Stated for the whole infinite
sequence of iterates, of which every `ε`-stopped call `Value-Iteration(u^0, ε)` is a prefix. -/
theorem valueIteration_geometric {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (πstar : Profile G) (hstar : IsOptimal G πstar)
    (u0 : S → ℝ) (k : ℕ) :
    ‖(valueIterOp G)^[k] u0 - value G πstar‖ ≤ G.γ ^ k * ‖u0 - value G πstar‖ := by sorry

end TBSGStrategyIteration
