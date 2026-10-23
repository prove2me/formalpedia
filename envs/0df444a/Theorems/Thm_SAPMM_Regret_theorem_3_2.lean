-- Prove2me | Theorems.Thm_SAPMM_Regret_theorem_3_2
-- name    : SAPMM.Regret.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:57.694212+00:00
-- url     : https://prove2.me/theorems/57c74acb-9293-4603-92d6-0b98c69429c6
-- title:
--   Theorem 3.2, pp. 14–15 — with α = √T, σ = T^{−1/2}: E[Σ_{t<T} F(x^t, ξ_t)] ≤ E[Σ_{t<T} F(x*, ξ_t)] + κ_o√T
-- statement:
--   Let $\xi_0,\xi_1,\dots$ be an i.i.d. sample (A1) on a probability space $(\Omega,\mathbb P)$ with values in the measurable space $\Xi$, and let the problem satisfy the standing assumptions of §1 and (A2)–(A4) with respect to the law of $\xi_0$. Fix a horizon $T\ge1$ and let $(x^t,\lambda^t)$ be the PMMSopt run with $\alpha=\sqrt T$ and $\sigma=T^{-1/2}$, started at $x^0\in X_0$. Then for every feasible point $x^*\in\Phi$,
--
--   $$
--   \mathbb E\Big[\sum_{t=0}^{T-1}F(x^t,\xi_t)\Big]\le\mathbb E\Big[\sum_{t=0}^{T-1}F(x^*,\xi_t)\Big]+\kappa_o\sqrt T,\qquad \kappa_o=\frac{\kappa_f^2}2+\frac{D_0^2}2+\frac{\nu_g^2}2.
--   $$
--
--   The expected cumulative objective of PMMSopt exceeds that of any feasible point by at most $O(\sqrt T)$, so the average objective regret is $O(T^{-1/2})$.
--
--   **Formalization Note** The paper takes $x^*$ to be a minimizer over $\Phi$ of $\sum_t f_t$ (with $f_t$ left undefined) and $T\ge2$; its proof uses only $x^*\in\Phi$ and holds for $T\ge1$, so the statement quantifies over every $x^*\in\Phi$ and every $T\ge1$ (more general). Slater's condition (A5) is not needed and not assumed. The hypothesis $x^0\in X_0$ corrects Step 0 (it is used through Lemma 3.1). Integrability of both sums follows from the finiteness of the expectations of $F$ and the bound $\nu_f$ on its oscillation.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, pp. 14–15, Theorem 3.2, (3.9)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Theorem 3.2, pp. 14–15, (3.9), for every feasible `x*` and every `T ≥ 1`. -/
theorem theorem_3_2 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (T : ℕ) (hT : 1 ≤ T)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P (1 / Real.sqrt T) (Real.sqrt T) x0 ξ x lam) :
    ∀ xs ∈ P.Phi (μ.map (ξ 0)),
      ∫ ω, ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω) ∂μ ≤
        ∫ ω, ∑ t ∈ Finset.range T, P.F xs (ξ t ω) ∂μ + P.κo * Real.sqrt T := by sorry

end SAPMM.Regret
