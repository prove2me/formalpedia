-- Prove2me | Theorems.Thm_SAPMM_Regret_theorems_3_1_3_2
-- name    : SAPMM.Regret.theorems_3_1_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:24:04.201663+00:00
-- url     : https://prove2.me/theorems/7a90e44e-cb6f-4d27-a5b6-042cfe83c36c
-- title:
--   Theorems 3.1 and 3.2, pp. 13–15 — with α = √T, σ = T^{−1/2}, PMMSopt has E[Σ G_i(x^t, ξ_t)] ≤ κ_c√T and E[Σ F(x^t, ξ_t)] ≤ E[Σ F(x*, ξ_t)] + κ_o√T
-- statement:
--   Let $\xi_0,\xi_1,\dots$ be an i.i.d. sample (A1) on a probability space $(\Omega,\mathbb P)$ with values in the measurable space $\Xi$, and let the problem satisfy the standing assumptions of §1 and (A2)–(A4) with respect to the law of $\xi_0$. Assume Slater's condition (A5). Fix a horizon $T\ge1$ with $3T>2p\kappa_g^2$, and let $(x^t,\lambda^t)$ be the PMMSopt run with $\alpha=\sqrt T$ and $\sigma=T^{-1/2}$, started at $x^0\in X_0$ with $\lambda^0=0$. Then:
--
--   1. (expected constraint violation) for every $i\in\{1,\dots,p\}$,
--   $$
--   \mathbb E\Big[\sum_{t=0}^{T-1}G_i(x^t,\xi_t)\Big]\le\kappa_c\sqrt T;
--   $$
--   2. (expected objective regret) for every feasible point $x^*\in\Phi$,
--   $$
--   \mathbb E\Big[\sum_{t=0}^{T-1}F(x^t,\xi_t)\Big]\le\mathbb E\Big[\sum_{t=0}^{T-1}F(x^*,\xi_t)\Big]+\kappa_o\sqrt T.
--   $$
--
--   Here $\kappa_c=\kappa_*+4\kappa_g\kappa_f+4\sqrt p\,(\kappa_*+\nu_g)\kappa_g^2$ with $\kappa_*=\kappa_0+\kappa_1+\kappa_3+2\kappa_4$ and $\kappa_0,\kappa_1,\kappa_3,\kappa_4$ from (3.1), and $\kappa_o=\kappa_f^2/2+D_0^2/2+\nu_g^2/2$. This is contribution (1) of the paper: with these step sizes both the constraint violation and the objective regret of $T$ iterations, averaged over $T$, are $O(T^{-1/2})$.
--
--   **Formalization Note** $\kappa_c$ is corrected relative to the printed $\kappa_*+4\kappa_g\kappa_f+2\sqrt p(\kappa_*+\nu_g)\kappa_g^2$ with $\kappa_*=\kappa_0+\kappa_1+\kappa_3+\kappa_4$, for the two reasons given under Theorem 3.1. The condition $3T>2p\kappa_g^2$ is the proof's own requirement (p. 13). Part 2 holds for every $x^*\in\Phi$ and every $T\ge1$, more general than the printed $x^*=\arg\min$ and $T\ge2$. The hypothesis $x^0\in X_0$ corrects Step 0, which prints $x^0\in\mathbb R^n$. Samples are indexed from $0$; norms are Euclidean.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, pp. 13–15, Theorems 3.1 and 3.2 (contribution (1), p. 4)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Theorems 3.1 and 3.2, pp. 13–15 (contribution (1), p. 4): with `α = √T`, `σ = 1/√T`, the
expected constraint violation and the expected objective regret of PMMSopt are `O(√T)`;
`κc` is the corrected constant. -/
theorem theorems_3_1_3_2 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (hS : P.Slater (μ.map (ξ 0))) (T : ℕ) (hT : 1 ≤ T)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P (1 / Real.sqrt T) (Real.sqrt T) x0 ξ x lam)
    (hTp : 2 * (p : ℝ) * P.κg ^ 2 < 3 * (T : ℝ)) :
    (∀ i, ∫ ω, ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ∂μ ≤ P.κc * Real.sqrt T) ∧
    (∀ xs ∈ P.Phi (μ.map (ξ 0)),
      ∫ ω, ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω) ∂μ ≤
        ∫ ω, ∑ t ∈ Finset.range T, P.F xs (ξ t ω) ∂μ + P.κo * Real.sqrt T) := by sorry

end SAPMM.Regret
