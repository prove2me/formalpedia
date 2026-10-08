-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_lemma2
-- name    : RobinsonFP.Convergence.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:20.808135+00:00
-- url     : https://prove2.me/theorems/1d0b70ae-10a7-48a5-955a-d02477b745b9
-- title:
--   Lemma 2 — if all rows and columns are eligible in (s, s+t), max U − min U ≤ 2at and max V − min V ≤ 2at
-- statement:
--   Let $A = (a_{ij})$ be a real $m \times n$ matrix with $m, n \ge 1$, let $a$ be a number with $|a_{ij}| \le a$ for all $i, j$, and let $(U, V)$ be a vector system for $A$. Let $s, t$ be nonnegative integers. If every row and every column of $A$ is eligible in the interval $(s, s+t)$ (Definition 2), then
--   $$\max U(s+t) - \min U(s+t) \le 2at \qquad\text{and}\qquad \max V(s+t) - \min V(s+t) \le 2at .$$
--
--   Once every row and column has been played during a window of length $t$, the spread of each accumulated payoff vector is at most linear in $t$, whatever the initial vectors were. Lemma 3 combines the two bounds.
--
--   **Formalization Note** The paper states the lemma with $a = \max_{i,j} |a_{ij}|$; we state it for every upper bound $a$ on the $|a_{ij}|$. This contains the paper's statement (take $a = \max_{i,j}|a_{ij}|$) and follows from it, since the right-hand side grows with $a$.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 298, Lemma 2

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 298, Lemma 2: if every row and every column is eligible in `(s, s + t)`,
then `max U(s+t) − min U(s+t) ≤ 2at` and `max V(s+t) − min V(s+t) ≤ 2at`, for any `a` bounding
every `|a_ij|` (in particular `a = max_{i,j} |a_ij|`). -/
theorem lemma2 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (U (s + t)) - vmin (U (s + t)) ≤ 2 * a * t ∧
      vmax (V (s + t)) - vmin (V (s + t)) ≤ 2 * a * t := by sorry

end RobinsonFP.Convergence
