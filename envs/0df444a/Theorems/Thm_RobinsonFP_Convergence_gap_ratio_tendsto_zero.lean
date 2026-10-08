-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_gap_ratio_tendsto_zero
-- name    : RobinsonFP.Convergence.gap_ratio_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:17.619136+00:00
-- url     : https://prove2.me/theorems/9d80469f-4a7f-492a-8fb4-61f44cce1497
-- title:
--   Proof of the Theorem, p. 301 — (max V(t) − min U(t))/t → 0
-- statement:
--   Let $A$ be a real $m \times n$ matrix with $m, n \ge 1$ and let $(U, V)$ be a vector system for $A$. Then
--   $$\lim_{t\to\infty} \frac{\max V(t) - \min U(t)}{t} = 0 .$$
--
--   This is the first step of the conclusion of the proof of the Theorem, obtained from Lemmas 1 and 4: the upper estimate $\max V(t)/t$ and the lower estimate $\min U(t)/t$ of the value come together.
--
--   **Formalization Note** Time runs over the natural numbers and the limit is along $t \to \infty$; the value at $t = 0$ (where Lean's division gives $0$) does not matter.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 301, proof of the Theorem (first display)

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 301, proof of the Theorem: `lim_{t→∞} (max V(t) − min U(t))/t = 0`. -/
theorem gap_ratio_tendsto_zero [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) :
    Tendsto (fun t : ℕ => (vmax (V t) - vmin (U t)) / t) atTop (𝓝 0) := by sorry

end RobinsonFP.Convergence
