-- Prove2me | Theorems.Thm_ProbMFG_Nash_eq_4_13
-- name    : ProbMFG.Nash.eq_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:22.991147+00:00
-- url     : https://prove2.me/theorems/c1b68daf-0461-48ac-a9b3-f90db56f9eb7
-- title:
--   (4.13), p. 2726 — W₂² of an empirical measure under a perturbation of its atoms
-- statement:
--   This is the elementary transport estimate behind (4.12) in the proof of Theorem 4.2 of Carmona and Delarue.
--
--   Let $N\ge1$, let $x_1,\dots,x_N$ and $y_1,\dots,y_N$ be points of $\mathbb R^d$, and let $\mu\in\mathcal P_2(\mathbb R^d)$. Then
--   $$W_2^2\Big(\frac1N\sum_{i=1}^N\delta_{x_i},\mu\Big)\le\frac2N\sum_{i=1}^N|x_i-y_i|^2 + 2W_2^2\Big(\frac1N\sum_{i=1}^N\delta_{y_i},\mu\Big).$$
--
--   In the paper it is applied with $x_i = X^i_t$ (the particle system), $y_i = \bar X^i_t$ (the decoupled copies) and $\mu = \mu_t$; taking expectations and using (4.11) and Lemma 4.1 yields (4.12).
--
--   **Formalization Note** $W_2$ takes values in $[0,\infty]$; both sides are compared in $[0,\infty]$, the first term on the right being the real number $\frac2N\sum_i|x_i-y_i|^2$. Norms are Euclidean.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2726, (4.13)

import Mathlib
import Definitions.Def_ProbMFG_Nash_Game

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbMFG.Nash

/-- (4.13), p. 2726: for points `x, y ∈ (ℝ^d)^N` and `μ ∈ 𝒫₂(ℝ^d)`,
`W₂²((1/N)Σδ_{x_i}, μ) ≤ (2/N) Σ |x_i − y_i|² + 2 W₂²((1/N)Σδ_{y_i}, μ)`. -/
theorem eq_4_13 {d : ℕ} (N : ℕ) (hN : 1 ≤ N) (x y : Fin N → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (hμ : IsP2 μ) :
    W2 (empirical x) μ ^ 2 ≤
      ENNReal.ofReal ((2 / (N : ℝ)) * ∑ i, ‖x i - y i‖ ^ 2) + 2 * W2 (empirical y) μ ^ 2 := by sorry

end ProbMFG.Nash
