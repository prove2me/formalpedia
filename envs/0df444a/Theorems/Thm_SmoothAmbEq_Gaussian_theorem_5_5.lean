-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_theorem_5_5
-- name    : SmoothAmbEq.Gaussian.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:24.78222+00:00
-- url     : https://prove2.me/theorems/b73f6224-823b-44ef-baaa-b6dbf7c489d1
-- title:
--   Theorem 5.5, p. 19 — π* of (5.12) is an equilibrium strategy with inside value function (5.8)–(5.9)
-- statement:
--   Consider the Gaussian-prior model: $dS_t/S_t=Z\,dt+\sigma dW_t$ with $Z\sim N(\beta_0,\sigma_0^2)$, CARA utility $U(x)=-\frac1ke^{-kx}$ and ambiguity function $\phi(u)=-\frac1\alpha(-u)^\alpha$ ($\alpha\ne0$), $\phi(u)=-\log(-u)$ ($\alpha=0$). Let $\alpha^*<0$ be the critical exponent of Proposition 5.4 and assume
--   $$\alpha>\max\Big\{\alpha^*,\ 1-0.5\,\sigma_0^{-2}\sigma^2T^{-1}\Big\}.$$
--   Let $m_1,\dots,m_6$ be given by Proposition 5.4 (the solution of (5.10)) and let
--   $$\pi^*(t,x,\beta)=\frac{e^{-r(T-t)}}{k\sigma^2}\big\{a_1(t,m_2(t),m_3(t))+\zeta(t)m_1(t)\big\}(\beta-r).\qquad(5.12)$$
--   Then:
--
--   1. $\pi^*$ is an equilibrium strategy in the sense of Definition 2.1, with the admissible class $\Pi$ of Definition 5.1;
--   2. the equilibrium value function for the inside expected utility is given by (5.8)–(5.9): for every $z\in\mathbb R$ and $(t,x,\beta)\in[0,T]\times\mathbb R^2$,
--   $$\mathbb E\big[U(X^{z,\pi^*}_T)\mid X^{z,\pi^*}_t=x,\ \beta^z_t=\beta\big]=g^z(t,x,\beta)=-\frac1k\exp\big\{-ke^{r(T-t)}x+f^z(t,\beta)\big\}.$$
--
--   This is the main result of the paper: a closed-form, time-consistent (equilibrium) investment rule for an investor who learns the drift and has smooth-ambiguity preferences. The rule is linear in the posterior mean $\beta$; its coefficient separates into myopic demand and two hedging demands.
--
--   **Formalization Note** The statement holds on every probability space carrying a Brownian motion. $(m_i)$ is any solution of (5.10) on $[0,T]$ keeping $\zeta^{-1}-\alpha m_3>0$; by Proposition 5.4 and (5.18) such a solution exists and is unique, and by Proposition 5.4 a unique $\alpha^*$ exists, so the hypotheses are satisfiable. The equilibrium predicate includes finiteness of $J$ for $\pi^*$ and for small spikes, and the $\limsup$ is in $\epsilon$-form (see the Equilibrium definition). The value identity is stated for every strong solution of the wealth equation of $\pi^*$, with integrability of $U(X_T)$ concluded; the paper's "$X^{\pi^*}_T=x$" in the conditioning of Theorems 3.5/4.5 is read as $X^{\pi^*}_t=x$ (paper.md slip 1). "Equilibrium solution" means equilibrium strategy (slip 11).
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 19, Theorem 5.5

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Theorem 5.5, p. 19. Assume `α > max{α*, 1 - 0.5σ₀⁻²σ²T⁻¹}` with `α*` of Proposition 5.4, let
`(mᵢ)` be the solution of (5.10) (Proposition 5.4 and (5.18)) and `π*` be given by (5.12). Then
`π*` is an equilibrium strategy (Definition 2.1 with the class `Π` of Definition 5.1), and the
equilibrium value function for the inside expected utility is `g^z` of (5.8)–(5.9):
`E[U(X^{z,π*}_T) | X^{z,π*}_t = x, β^z_t = β] = g^z(t, x, β)` for all `z` and `(t, x, β) ∈ [0, T] × ℝ²`. -/
theorem theorem_5_5 (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    IsEquilibrium M P W (piStar M c) ∧
    ∀ z : ℝ, ∀ t ∈ Icc 0 M.T, ∀ x β : ℝ, ∀ X : ℝ → Ω → ℝ,
      IsInsideWealth M P W (piStar M c) z t x β X →
        Integrable (fun ω => M.U (X M.T ω)) P ∧ ∫ ω, M.U (X M.T ω) ∂P = gz M c z t x β := by sorry

end SmoothAmbEq.Gaussian
