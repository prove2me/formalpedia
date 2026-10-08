-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_lemma3
-- name    : RobinsonFP.Convergence.lemma3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:13.876988+00:00
-- url     : https://prove2.me/theorems/e194120b-1be3-487b-aee4-fb64ef6d6637
-- title:
--   Lemma 3 — if all rows and columns are eligible in (s, s+t), max V(s+t) − min U(s+t) ≤ 4at
-- statement:
--   Let $A = (a_{ij})$ be a real $m \times n$ matrix with $m, n \ge 1$, let $a$ be a number with $|a_{ij}| \le a$ for all $i, j$, and let $(U, V)$ be a vector system for $A$. Let $s, t$ be nonnegative integers. If every row and every column of $A$ is eligible in the interval $(s, s+t)$, then
--   $$\max V(s+t) - \min U(s+t) \;\le\; 4at .$$
--
--   This bounds the gap between the two estimates of the value after a window in which every pure strategy has been a best reply. It is the case of the proof of Lemma 4 in which no row or column can be deleted.
--
--   **Formalization Note** The paper's $a$ is $\max_{i,j}|a_{ij}|$; we state the lemma for every upper bound $a$ on the $|a_{ij}|$, which is equivalent (see Lemma 2). The hypothesis that $(U, V)$ is a vector system, including $\min U(0) = \max V(0)$, is essential and kept.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 299, Lemma 3

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 299, Lemma 3: if every row and every column is eligible in `(s, s + t)`,
then `max V(s+t) − min U(s+t) ≤ 4at`, for any `a` bounding every `|a_ij|`. -/
theorem lemma3 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (V (s + t)) - vmin (U (s + t)) ≤ 4 * a * t := by sorry

end RobinsonFP.Convergence
