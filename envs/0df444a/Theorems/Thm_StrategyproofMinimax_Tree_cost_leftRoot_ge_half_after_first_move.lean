-- Prove2me | Theorems.Thm_StrategyproofMinimax_Tree_cost_leftRoot_ge_half_after_first_move
-- name    : StrategyproofMinimax.Tree.cost_leftRoot_ge_half_after_first_move
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:09:59.057735+00:00
-- url     : https://prove2.me/theorems/1aa5bd48-bdba-489c-951a-e9ee574bdb8a
-- title:
--   Appendix B, p. 524 — the bound 𝔼[d(f(x¹), l⁰)] ≥ 1/2 survives the first move
-- statement:
--   Let $f:G^n\to\Delta(G)$ be a strategyproof randomized mechanism on the tree $G=G(m,k)$, with $2m^k$ dividing $n$, and suppose that under the profile $x^0$ ($n/2$ agents at $l^0$, $n/2$ at $r^0$) the facility is in expectation at distance at least $1/2$ from $l^0$. Then the same holds under the profile $x^1$, which has $n/(2m)$ agents at each left vertex on level 1 and $n/2$ agents at $r^0$:
--   $$\mathbb E\big[d(f(x^0),l^0)\big]\ge\tfrac12\ \Longrightarrow\ \mathbb E\big[d(f(x^1),l^0)\big]\ge\tfrac12 .$$
--   This is the first step of the proof of Theorem 4.1: strategyproofness keeps the facility far from the vertex the agents have left.
--
--   **Formalization Note.** $\mathbb E[d(f(x),l^0)]$ is `cost (f x) (vertex .left [])`; $x^0$ is `profileZero m k n` and $x^1$ is `profileAlong m k n []`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 524, Appendix B (claim on the profile x¹)

import Mathlib
import Definitions.Def_StrategyproofMinimax_Tree_cost
import Definitions.Def_StrategyproofMinimax_Tree_HardTree
import Definitions.Def_StrategyproofMinimax_Tree_profileAlong

namespace StrategyproofMinimax.Tree

/-- Appendix B, p. 524: if `𝔼[d(f(x⁰), l⁰)] ≥ 1/2` for an SP mechanism `f` on `G(m, k)`, then
still `𝔼[d(f(x¹), l⁰)] ≥ 1/2`, where `x¹` has `n/(2m)` agents at each left vertex on level 1 and
`n/2` agents at `r⁰`. -/
theorem cost_leftRoot_ge_half_after_first_move {m k n : ℕ} (hdiv : 2 * m ^ k ∣ n)
    (f : (Fin n → HardTree m k) → MeasureTheory.ProbabilityMeasure (HardTree m k))
    (hf : IsStrategyproof f)
    (h0 : (1 : ℝ) / 2 ≤ cost (f (profileZero m k n)) (vertex .left [])) :
    (1 : ℝ) / 2 ≤ cost (f (profileAlong m k n [])) (vertex .left []) := by sorry

end StrategyproofMinimax.Tree
