-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_lemma4
-- name    : RobinsonFP.Convergence.lemma4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:26.621012+00:00
-- url     : https://prove2.me/theorems/3d7a07b3-1701-4ce0-900e-a5936266230d
-- title:
--   Lemma 4 — there is t₀, uniform over vector systems, with max V(t) − min U(t) < εt for t ≥ t₀
-- statement:
--   Let $A$ be a real $m \times n$ matrix with $m, n \ge 1$ and let $\varepsilon > 0$. There is a nonnegative integer $t_0$, depending only on $A$ and $\varepsilon$, such that every vector system $(U, V)$ for $A$ satisfies
--   $$\max V(t) - \min U(t) \;<\; \varepsilon t \qquad\text{for all } t \ge t_0 .$$
--
--   The point is the uniformity: one $t_0$ serves every vector system, whatever its initial vectors and tie-breaking, which is what lets the proof proceed by induction over submatrices. With Lemma 1 it gives $(\max V(t) - \min U(t))/t \to 0$.
--
--   **Formalization Note** The order of quantifiers is $\exists t_0\ \forall (U, V)\ \forall t \ge t_0$, as in the paper. The matrix is fixed in the statement; a proof will typically generalize over the index types to run the induction over submatrices.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 299, Lemma 4

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 299, Lemma 4: for every matrix `A` and `ε > 0` there is `t₀`, depending
only on `A` and `ε`, such that every vector system `(U, V)` for `A` satisfies
`max V(t) − min U(t) < εt` for all `t ≥ t₀`. -/
theorem lemma4 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℕ, ∀ (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ), IsVectorSystem A U V →
      ∀ t : ℕ, t₀ ≤ t → vmax (V t) - vmin (U t) < ε * t := by sorry

end RobinsonFP.Convergence
