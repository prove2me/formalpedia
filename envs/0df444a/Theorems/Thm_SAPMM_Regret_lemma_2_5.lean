-- Prove2me | Theorems.Thm_SAPMM_Regret_lemma_2_5
-- name    : SAPMM.Regret.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:36.261984+00:00
-- url     : https://prove2.me/theorems/02b867b0-2a57-474e-9222-45b5cee8ddc1
-- title:
--   Lemma 2.5, p. 8 — E[⟨λ^{t_1}, G(x̂, ξ_{t_1})⟩ | history] ≤ −ε_0 E[‖λ^{t_1}‖ | history], (2.12)
-- statement:
--   Let $\xi_0,\xi_1,\dots$ be an i.i.d. sample (A1) on a probability space $(\Omega,\mathbb P)$ with values in the measurable space $\Xi$, and let the problem satisfy the standing assumptions of §1 and (A2)–(A4) with respect to the law of $\xi_0$. Assume Slater's condition (A5) with point $\hat x$ and margin $\epsilon_0$. Let $(x^t,\lambda^t)$ be the PMMSopt run with parameters $\sigma,\alpha>0$, started at $x^0\in X_0$, and let $\mathcal H_k=\sigma(\xi_0,\dots,\xi_{k-1})$.
--
--   Then for all integers $0\le k\le t_1$, almost surely,
--
--   $$
--   \mathbb E\big[\langle\lambda^{t_1},G(\hat x,\xi_{t_1})\rangle\,\big|\,\mathcal H_k\big]\le-\epsilon_0\,\mathbb E\big[\|\lambda^{t_1}\|\,\big|\,\mathcal H_k\big].
--   $$
--
--   The multiplier $\lambda^{t_1}$ is determined by the samples before time $t_1$, while $\xi_{t_1}$ is fresh; Slater's condition then makes the Lagrangian term at $\hat x$ push the multiplier norm down. This is the source of the negative drift in Lemma 2.6.
--
--   **Formalization Note** The paper's $\xi_{[t_2]}$ with positive integers $t_2\le t_1-1$ is $\mathcal H_{t_2+1}$ (`hist ξ (t2+1)`), i.e. $2\le k\le t_1$; the statement allows every $k\le t_1$, which is more general. The page lists (A1), (A2), (A5); the bounds of (A3)–(A4) and the standing assumptions are also assumed, since they make the integrands integrable. The hypothesis $x^0\in X_0$ corrects Step 0.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 8, Lemma 2.5, (2.12)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Lemma 2.5, p. 8, (2.12): conditional Slater bound. The paper's `ξ_[t2]` with
`1 ≤ t2 ≤ t1 - 1` is `hist ξ (t2 + 1)`; here every `hist ξ k` with `k ≤ t1` is allowed. -/
theorem lemma_2_5 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (hS : P.Slater (μ.map (ξ 0))) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ t1 k : ℕ, k ≤ t1 →
      μ[fun ω => inner ℝ (lam t1 ω) (P.G P.xhat (ξ t1 ω)) | hist ξ k] ≤ᵐ[μ]
        fun ω => -P.ε0 * μ[fun ω => ‖lam t1 ω‖ | hist ξ k] ω := by sorry

end SAPMM.Regret
