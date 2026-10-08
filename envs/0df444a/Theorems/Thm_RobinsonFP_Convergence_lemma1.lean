-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_lemma1
-- name    : RobinsonFP.Convergence.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:14.469459+00:00
-- url     : https://prove2.me/theorems/4d82ed09-8fd5-4ee3-b772-fc7729aebd1e
-- title:
--   Lemma 1 — lim inf (max V(t) − min U(t))/t ≥ 0
-- statement:
--   Let $A$ be a real $m \times n$ matrix with $m, n \ge 1$ and let $(U, V)$ be a vector system for $A$ (Definition 1). Then
--   $$\liminf_{t\to\infty} \frac{\max V(t) - \min U(t)}{t} \;\ge\; 0 .$$
--
--   The gap $\max V(t) - \min U(t)$ is, after division by $t$, the difference between the upper and lower estimates of the value produced by the iteration; Lemma 1 says it cannot become negative at a linear rate. Together with Lemma 4 it shows that the gap is $o(t)$.
--
--   **Formalization Note** The lim inf is stated in $\varepsilon$-form: for every $\varepsilon > 0$ there is $T$ with $(\max V(t) - \min U(t))/t \ge -\varepsilon$ for all integers $t \ge T$. This is equivalent to the extended-real lim inf being $\ge 0$ and needs no boundedness assumption. At $t = 0$ Lean's division gives $0$; this does not affect an eventual statement.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 297, Lemma 1

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 297, Lemma 1: `lim inf_{t→∞} (max V(t) − min U(t))/t ≥ 0`, stated in
ε-form: for every `ε > 0`, eventually `(max V(t) − min U(t))/t ≥ −ε`. -/
theorem lemma1 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, -ε ≤ (vmax (V t) - vmin (U t)) / t := by sorry

end RobinsonFP.Convergence
