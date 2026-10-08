-- Prove2me | Theorems.Thm_SuttonTD_Convergence_theorem_A_1
-- name    : SuttonTD.Convergence.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:41.75382+00:00
-- url     : https://prove2.me/theorems/76a90eb2-7150-47e1-bd39-abc316f7bbf4
-- title:
--   Theorem A.1 — $A^n\to0$ implies $(I-A)^{-1}=\sum_i A^i$
-- statement:
--   Let $A$ be a real square matrix with
--
--   $$\lim_{n\to\infty}A^n=0 .$$
--
--   Then $I-A$ is invertible, and the Neumann series converges to its inverse:
--
--   $$(I-A)^{-1}=\sum_{i=0}^{\infty}A^i .$$
--
--   This is used to justify the formula $[(I-Q)^{-1}h]_i$ for the ideal predictions and the limit of the mean TD(0) recursion.
--
--   **Formalization Note** Convergence of the series is part of the statement (`HasSum`).
-- source:
--   Sutton (1988), Machine Learning 3:9–44, Appendix, Theorem A.1, p. 44 (PDF p. 36)

import Mathlib
open Filter Topology

namespace SuttonTD.Convergence

/-- **Theorem A.1** (Sutton 1988, Appendix, p. 44, PDF p. 36): "If `lim_{n→∞} Aⁿ = 0`, then
`I − A` has an inverse, and `(I − A)⁻¹ = ∑_{i=0}^∞ Aⁱ`."

Formalization Note: the series is stated with `HasSum`, so it asserts convergence and not only
the value of a `tsum` (which would be `0` for a divergent series). `A` is any square real matrix
indexed by a finite type. -/
theorem theorem_A_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0)) :
    IsUnit (1 - A) ∧ HasSum (fun i : ℕ => A ^ i) (1 - A)⁻¹ := by sorry

end SuttonTD.Convergence
