-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_corollary_5_6
-- name    : ReserveLP.ProLPR.corollary_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:20.379432+00:00
-- url     : https://prove2.me/theorems/b525acb0-bcf8-46b0-9060-c7ef5036dc56
-- title:
--   Corollary 5.6, p. 16 — OPT(θ) ≤ max over k ≥ 2 of max[OPT¹(θ, k), OPT²(θ, k)]
-- statement:
--   Let $n\ge2$ and $\theta\in[0,1]$, and let $\mathsf{OPT}(\theta)$ be the optimal value of Problem (10) with $n$ variables. Then
--
--   $$\mathsf{OPT}(\theta)\ \le\ \max_{k\in\mathbb Z,\ k\ge2}\ \max\big[\mathsf{OPT}^1(\theta,k),\ \mathsf{OPT}^2(\theta,k)\big],$$
--
--   with $\mathsf{OPT}^1,\mathsf{OPT}^2$ as in the model file. The statement says the maximum of Problem (10) is attained on one of two symmetric families of candidate points.
--
--   **Formalization Note.**
--   1. The maximum over $k$ is not formed. The statement says that any $M$ bounding $\mathsf{OPT}^1(\theta,k)$ and $\mathsf{OPT}^2(\theta,k)$ for all $k\ge2$ also bounds $\mathsf{OPT}(\theta)$. This is equivalent to the displayed inequality with a supremum over $k$.
--   2. The printed proof relies on Lemma 5.5, which is false as printed: $n=3$, $\theta=\tfrac12$, $x=(0.2,0.3,0.5)$ satisfies the KKT system with two unequal interior coordinates. The corollary itself agrees with numerical optimization of Problem (10) for $n\le 20$, but it needs a different proof.
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, p. 16, Corollary 5.6

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR

theorem corollary_5_6 (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (M : ℝ)
    (hM : ∀ k : ℕ, 2 ≤ k → OPT1 θ k ≤ M ∧ OPT2 θ k ≤ M) :
    OPT n θ ≤ M := by sorry

end ReserveLP.ProLPR
