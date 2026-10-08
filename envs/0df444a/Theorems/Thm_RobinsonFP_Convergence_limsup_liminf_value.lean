-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_limsup_liminf_value
-- name    : RobinsonFP.Convergence.limsup_liminf_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:25.516348+00:00
-- url     : https://prove2.me/theorems/90a2df2a-63a5-4229-82f9-aeaa87d1e843
-- title:
--   Proof of the Theorem, p. 301 — lim sup min U(t)/t ≤ v and lim inf max V(t)/t ≥ v
-- statement:
--   Let $A$ be a real $m \times n$ matrix with $m, n \ge 1$, let $(X, Y)$ be a solution of the game $A$ with value $v$, and let $(U, V)$ be a vector system for $A$. Then
--   $$\limsup_{t\to\infty} \frac{\min U(t)}{t} \le v, \qquad \liminf_{t\to\infty} \frac{\max V(t)}{t} \ge v .$$
--
--   The lower estimate cannot exceed the value and the upper estimate cannot fall below it, asymptotically; with the previous step this pins both limits at $v$.
--
--   **Formalization Note** Both are stated together in $\varepsilon$-form: for every $\varepsilon > 0$, for all sufficiently large $t$, $\min U(t)/t \le v + \varepsilon$ and $\max V(t)/t \ge v - \varepsilon$. The value $v$ is tied to a solution $(X, Y)$ through `IsSolution A x y v`, exactly as the paper defines it on p. 296; such a solution exists for every matrix by the minimax theorem (proved on Prove2Me as `MatousekLP.ZeroSum.minimax_equality`, in another encoding).
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 301, proof of the Theorem (second display)

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 301, proof of the Theorem: `lim sup_{t→∞} min U(t)/t ≤ v` and
`lim inf_{t→∞} max V(t)/t ≥ v`, where `v` is the value of the game, stated in ε-form. -/
theorem limsup_liminf_value [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V)
    (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) (hsol : IsSolution A x y v) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop,
      vmin (U t) / t ≤ v + ε ∧ v - ε ≤ vmax (V t) / t := by sorry

end RobinsonFP.Convergence
