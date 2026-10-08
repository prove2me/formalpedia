-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_robinson_theorem
-- name    : RobinsonFP.Convergence.robinson_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:41.764479+00:00
-- url     : https://prove2.me/theorems/23fc086c-d590-4214-8926-8fabda7e5741
-- title:
--   Theorem (Robinson 1951) — for every vector system, min U(t)/t → v and max V(t)/t → v
-- statement:
--   Let $A = (a_{ij})$ be a real $m \times n$ matrix with $m, n \ge 1$, the pay-off matrix of a finite two-person zero-sum game, and let $v$ be its value, given by a solution $(X, Y)$ of the game. If $(U, V)$ is a vector system for $A$ (Definition 1), then
--   $$\lim_{t\to\infty} \frac{\min U(t)}{t} \;=\; \lim_{t\to\infty} \frac{\max V(t)}{t} \;=\; v .$$
--
--   This is the convergence of Brown's iterative method (fictitious play) for zero-sum matrix games: when each player in turn plays a best pure reply to the accumulated play of the opponent, the lower and upper estimates of the value obtained from the accumulated payoffs both converge to the value of the game. The statement holds for arbitrary initial vectors with $\min U(0) = \max V(0)$ and for every tie-breaking rule.
--
--   **Formalization Note** Rows and columns are indexed by finite nonempty types. The value $v$ enters through `IsSolution A x y v` (probability vectors $x$, $y$ with $\min_j \sum_i a_{ij}x_i = v = \max_i \sum_j a_{ij} y_j$), as defined on p. 296; a solution exists for every matrix by the minimax theorem (proved on Prove2Me as `MatousekLP.ZeroSum.minimax_equality`, in another encoding), so the hypothesis is satisfiable. The two limits are stated as `Tendsto … atTop (𝓝 v)` along $t \in \mathbb N$. The paper's closing display on p. 301 prints $\lim \min V(t)/t$; the intended reading, confirmed by the statement of the Theorem on p. 297 and the lim sup display just above it, is $\lim \min U(t)/t$, which is what is stated here.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 297, Theorem

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 297, Theorem: if `(U, V)` is a vector system for `A`, then
`lim_{t→∞} min U(t)/t = lim_{t→∞} max V(t)/t = v`, the value of the game. -/
theorem robinson_theorem [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V)
    (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) (hsol : IsSolution A x y v) :
    Tendsto (fun t : ℕ => vmin (U t) / t) atTop (𝓝 v) ∧
      Tendsto (fun t : ℕ => vmax (V t) / t) atTop (𝓝 v) := by sorry

end RobinsonFP.Convergence
