-- Prove2me | Theorems.Thm_SAPMM_Regret_lemma_2_6
-- name    : SAPMM.Regret.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:31.519266+00:00
-- url     : https://prove2.me/theorems/67f2e52b-4dd1-415a-a4b8-8a0d2f329d52
-- title:
--   Lemma 2.6, p. 9 — conditional drift of ‖λ^t‖ over s steps with threshold ϑ(σ, α, s), (2.14)–(2.15)
-- statement:
--   Let $\xi_0,\xi_1,\dots$ be an i.i.d. sample (A1) on a probability space $(\Omega,\mathbb P)$ with values in the measurable space $\Xi$, and let the problem satisfy the standing assumptions of §1 and (A2)–(A4) with respect to the law of $\xi_0$. Assume Slater's condition (A5). Let $(x^t,\lambda^t)$ be the PMMSopt run with parameters $\sigma,\alpha>0$, started at $x^0\in X_0$, and let $\mathcal H_t=\sigma(\xi_0,\dots,\xi_{t-1})$. Let $s\ge1$ be an integer and
--
--   $$
--   \vartheta(\sigma,\alpha,s)=\frac{\epsilon_0\sigma s}2+\nu_g\sigma(s-1)+\frac{\alpha D_0^2}{\epsilon_0 s}+\frac{2\nu_f}{\epsilon_0}+\frac{\sigma\nu_g^2}{\epsilon_0}.
--   $$
--
--   Then for every $t\ge1$: $\big|\|\lambda^{t+1}\|-\|\lambda^t\|\big|\le\sigma\nu_g$ everywhere, and almost surely
--
--   $$
--   \mathbb E\big[\|\lambda^{t+s}\|-\|\lambda^t\|\,\big|\,\mathcal H_t\big]\le\begin{cases}s\sigma\nu_g&\text{if }\|\lambda^t\|<\vartheta(\sigma,\alpha,s),\\-s\sigma\epsilon_0/2&\text{if }\|\lambda^t\|\ge\vartheta(\sigma,\alpha,s).\end{cases}
--   $$
--
--   These are exactly the hypotheses of the drift lemma (Lemma 2.7) for the process $Z(t)=\|\lambda^t\|$, with $t_0=s$, $\delta_{\max}=\sigma\nu_g$, $\zeta=\sigma\epsilon_0/2$ and $\theta=\vartheta(\sigma,\alpha,s)$.
--
--   **Formalization Note** The paper conditions on $\xi_{[t-1]}$, which is $\mathcal H_t$ (`hist ξ t`) with 0-based samples. The page cites (A1)–(A4) only, but $\vartheta$ contains $\epsilon_0$ and the proof uses $\hat x$ through Lemma 2.5, so (A5) is assumed. The hypothesis $x^0\in X_0$ corrects Step 0.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 9, Lemma 2.6, (2.13)–(2.15)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Lemma 2.6, p. 9, (2.14)–(2.15): conditional drift of `‖λ^t‖` over `s` steps. The paper's
`ξ_[t-1]` is `hist ξ t`. (A5) is assumed: `ϑ` and the proof use `ε0` and `x̂`. -/
theorem lemma_2_6 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (hS : P.Slater (μ.map (ξ 0))) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam)
    (s : ℕ) (hs : 1 ≤ s) (t : ℕ) (ht : 1 ≤ t) :
    (∀ ω, |‖lam (t + 1) ω‖ - ‖lam t ω‖| ≤ σ * P.νg) ∧
      ∀ᵐ ω ∂μ, μ[fun ω => ‖lam (t + s) ω‖ - ‖lam t ω‖ | hist ξ t] ω ≤
        if ‖lam t ω‖ < P.vartheta σ α s then (s : ℝ) * σ * P.νg
        else -((s : ℝ) * σ * P.ε0 / 2) := by sorry

end SAPMM.Regret
