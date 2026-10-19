-- Prove2me | Theorems.Thm_TerminalRank_Equilibrium_theorem_3_2
-- name    : TerminalRank.Equilibrium.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:20.106229+00:00
-- url     : https://prove2.me/theorems/f7ae7ecd-d9f9-4d09-baf9-c7ce5dbb5256
-- title:
--   Theorem 3.2, pp. 7–8 — rank-based mean field tournament: an equilibrium exists, equilibria are exactly the quantile formula (3.2) with mean solving (3.3), explicit value
-- statement:
--   Fix $T>0$, a cost coefficient $c>0$, a volatility $\sigma>0$ and $x_0\in\mathbb R$; let $B$ be a Brownian motion under $P$ and $X_T=x_0+\sigma B_T$. Let $R=R(r,m)\in\mathcal R^{rm}_b$ be a bounded reward, weakly increasing in the rank $r\in[0,1]$ and in the population mean $m$, and continuous in $m$. Write $N$ for the standard normal c.d.f. Then:
--
--   1. there exists at least one equilibrium;
--   2. a probability measure $\mu$ on $\mathbb R$ is an equilibrium if and only if it has a finite mean $m_\mu=\int y\,d\mu(y)$, its quantile function $q_\mu$ satisfies, for every $r\in(0,1)$,
--   $$q_\mu(r)=x_0+\sigma\sqrt T\,N^{-1}\!\left(\frac{\int_0^r\exp\big(-\frac{R(z,m_\mu)}{2c\sigma^2}\big)dz}{\int_0^1\exp\big(-\frac{R(z,m_\mu)}{2c\sigma^2}\big)dz}\right), \tag{3.2}$$
--   and $m=m_\mu$ solves
--   $$m=x_0+\sigma\sqrt T\int_0^1N^{-1}\!\left(\frac{\int_0^r\exp\big(-\frac{R(z,m)}{2c\sigma^2}\big)dz}{\int_0^1\exp\big(-\frac{R(z,m)}{2c\sigma^2}\big)dz}\right)dr; \tag{3.3}$$
--   3. for every equilibrium $\mu$ the game value is
--   $$V(R,\mu)=2c\sigma^2\ln\beta(\mu)=-2c\sigma^2\ln\Big(\int_0^1\exp\Big(-\frac{R(z,m_\mu)}{2c\sigma^2}\Big)dz\Big).$$
--
--   This is the paper's semi-explicit solution of the mean field tournament: the equilibrium law is determined by one scalar, the mean, which solves a one-dimensional fixed-point equation, and the game value is explicit.
--
--   **Formalization Note.** $V$ and the equilibrium are defined from the path-space control problem (2.3), not from these formulas. The equation (3.2) is required for $r\in(0,1)$ (at $r=0,1$ its right side is $\mp\infty$), and $q_\mu(r)=\inf\{x:r\le F_\mu(x)\}$ is the left-continuous quantile. The finite mean is stated explicitly because Lean's integral is $0$ for a non-integrable function; every equilibrium has Gaussian tails, so this does not weaken the equivalence. The reward $R(r,m)$ enters the general model as $R(x,r,m)=R(r,m)$. The theorem does not claim uniqueness.
-- source:
--   Bayraktar & Zhang, Terminal Ranking Games, arXiv:1906.09628v2, pp. 7–8, Theorem 3.2, (3.2), (3.3)

import Mathlib
import Definitions.Def_TerminalRank_Equilibrium_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TerminalRank.Equilibrium

/-- Theorem 3.2, pp. 7–8 (Bayraktar–Zhang, arXiv:1906.09628v2). For `R ∈ ℛʳᵐ_b`:
1. an equilibrium exists;
2. a probability measure `µ` is an equilibrium iff it has a finite mean `m_µ`, its quantile
   function satisfies (3.2) `q_µ(r) = x0 + σ√T N⁻¹(ratio(m_µ, r))` for `r ∈ (0, 1)`, and `m_µ`
   solves (3.3) `m = g(m)`;
3. the game value of an equilibrium is
   `V(R, µ) = 2cσ² ln β(µ) = −2cσ² ln ∫_0^1 exp(−R(z, m_µ)/(2cσ²)) dz`.
Conventions: (3.2) is required on `r ∈ (0, 1)` (at 0, 1 the right side is ∓∞); `q_µ` is the
left-continuous quantile `inf {x | r ≤ F_µ(x)}`; integrability of `y` under `µ` makes `m_µ` the
mean (every equilibrium has Gaussian tails, so this does not weaken the equivalence). -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] (x0 σ c : ℝ) (T : ℝ≥0)
    (hσ : 0 < σ) (hc : 0 < c) (hT : 0 < T)
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (R : ℝ → ℝ → ℝ) (hR : IsRMReward R) :
    (∃ μ : Measure ℝ, IsEquilibrium x0 σ c T P B (lift R) μ) ∧
    (∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      (IsEquilibrium x0 σ c T P B (lift R) μ ↔
        (Integrable (fun y : ℝ => y) μ ∧
          (∀ r ∈ Set.Ioo (0 : ℝ) 1,
            quantile μ r = x0 + σ * Real.sqrt T * Ninv (ratio σ c R (meanOf μ) r)) ∧
          meanOf μ = gmap x0 σ c T R (meanOf μ)))) ∧
    (∀ μ : Measure ℝ, IsEquilibrium x0 σ c T P B (lift R) μ →
      V x0 σ c T P B (lift R) μ = 2 * c * σ ^ 2 * Real.log (beta x0 σ c T (lift R) μ) ∧
      V x0 σ c T P B (lift R) μ = -(2 * c * σ ^ 2) *
        Real.log (∫ z in (0 : ℝ)..1, Real.exp (-R z (meanOf μ) / (2 * c * σ ^ 2)))) := by sorry

end TerminalRank.Equilibrium
