-- Prove2me | Theorems.Thm_SAPMM_Regret_theorem_3_1
-- name    : SAPMM.Regret.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:24:05.646595+00:00
-- url     : https://prove2.me/theorems/dbb64cd5-b7d8-407f-9ef5-b102c3e840b5
-- title:
--   Theorem 3.1, p. 13 (corrected κ_c) — with α = √T, σ = T^{−1/2}: E[Σ_{t<T} G_i(x^t, ξ_t)] ≤ κ_c√T
-- statement:
--   Let $\xi_0,\xi_1,\dots$ be an i.i.d. sample (A1) on a probability space $(\Omega,\mathbb P)$ with values in the measurable space $\Xi$, and let the problem satisfy the standing assumptions of §1 and (A2)–(A4) with respect to the law of $\xi_0$. Assume Slater's condition (A5). Fix a horizon $T\ge1$ with $3T>2p\kappa_g^2$, and let $(x^t,\lambda^t)$ be the PMMSopt run with $\alpha=\sqrt T$ and $\sigma=T^{-1/2}$, started at $x^0\in X_0$. Then for every $i\in\{1,\dots,p\}$,
--
--   $$
--   \mathbb E\Big[\sum_{t=0}^{T-1}G_i(x^t,\xi_t)\Big]\le\kappa_c\sqrt T,\qquad \kappa_c=\kappa_*+4\kappa_g\kappa_f+4\sqrt p\,(\kappa_*+\nu_g)\kappa_g^2,\quad \kappa_*=\kappa_0+\kappa_1+\kappa_3+2\kappa_4,
--   $$
--
--   with $\kappa_0,\kappa_1,\kappa_3,\kappa_4$ as in (3.1). The cumulative expected constraint violation therefore grows like $\sqrt T$, so its average over $T$ steps is $O(T^{-1/2})$.
--
--   **Corrections.** (i) The paper's proof bounds $\mathbb E\|\lambda^t\|\le\kappa_0+\kappa_1\alpha/s+\kappa_3\sigma+\kappa_4\sigma s$ with $s=\lceil\sqrt T\rceil$; there $\kappa_4\sigma s=\kappa_4\lceil\sqrt T\rceil/\sqrt T$ is at most $2\kappa_4$ but exceeds $\kappa_4$ unless $T$ is a perfect square, so $\kappa_*$ takes $2\kappa_4$ (printed: $\kappa_4$). (ii) Corollary 2.1 carries doubled coefficients (see Lemma 2.4), which turns the printed $2\sqrt p$ into $4\sqrt p$. With both corrections the paper's proof goes through as written.
--
--   **Formalization Note** The condition $3T>2p\kappa_g^2$ is the proof's own requirement $2\sqrt T-p\kappa_g^2\sigma>\sqrt T/2$ (p. 13) with $\sigma=T^{-1/2}$; the theorem's "for all $T\ge1$" omits it. The hypothesis $x^0\in X_0$ corrects Step 0. Integrability of the sum follows from the boundedness of $G$ and the measurability of the iterates.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 13, Theorem 3.1, (3.2) (constant corrected; proof p. 13)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Theorem 3.1, p. 13, with the **corrected** `κc` (see `Problem.κc`) and the proof's condition
`3T > 2pκg²` (`2√T - pκg²σ > √T/2`). -/
theorem theorem_3_1 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (hS : P.Slater (μ.map (ξ 0))) (T : ℕ) (hT : 1 ≤ T)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P (1 / Real.sqrt T) (Real.sqrt T) x0 ξ x lam)
    (hTp : 2 * (p : ℝ) * P.κg ^ 2 < 3 * (T : ℝ)) :
    ∀ i, ∫ ω, ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ∂μ ≤ P.κc * Real.sqrt T := by sorry

end SAPMM.Regret
