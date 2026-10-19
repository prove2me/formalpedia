-- Prove2me | Theorems.Thm_TerminalRank_Equilibrium_theorem_3_1
-- name    : TerminalRank.Equilibrium.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:05.123701+00:00
-- url     : https://prove2.me/theorems/66ebdd9c-9c19-4240-baca-cd09aba2fb50
-- title:
--   Theorem 3.1, p. 7, for R ∈ ℛ_b — equilibria are exactly the laws with positive density solving the fixed-point equation (3.1)
-- statement:
--   Under the standing data, let $R\in\mathcal R_b$ and let $\mu$ be a probability measure on $\mathbb R$ with $\beta(\mu)=\int f_0(y)\exp(R_\mu(y)/2c\sigma^2)\,dy$. Then $\mu$ is an equilibrium if and only if $\mu$ has a strictly positive density $f_\mu$ with
--   $$f_\mu(x)=\frac{1}{\beta(\mu)}f_0(x)\exp\Big(\frac{R_\mu(x)}{2c\sigma^2}\Big)\qquad(x\in\mathbb R). \tag{3.1}$$
--   Moreover, if $\mu$ is an equilibrium, the associated game value is $V(R,\mu)=2c\sigma^2\ln\beta(\mu)$.
--
--   The theorem turns the fixed point of the best-response map, defined through the path-space control problem, into a fixed-point equation for a density on the real line.
--
--   **Formalization Note.** The paper states the theorem for $R\in\mathcal R$ under $\beta(\mu)<\infty$ and notes that the condition always holds for $R\in\mathcal R_b$; this formalization covers that case.
-- source:
--   Bayraktar & Zhang, Terminal Ranking Games, arXiv:1906.09628v2, p. 7, Theorem 3.1, (3.1)

import Mathlib
import Definitions.Def_TerminalRank_Equilibrium_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TerminalRank.Equilibrium

/-- Theorem 3.1, p. 7 (Bayraktar–Zhang, arXiv:1906.09628v2), for `R ∈ ℛ_b` (the case named in the
theorem's parenthesis, where `β(µ) < ∞` always holds): `µ` is an equilibrium iff it has a strictly
positive density `f_µ = f0 exp(R_µ/(2cσ²)) / β(µ)` (3.1); the game value is then `2cσ² ln β(µ)`. -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] (x0 σ c : ℝ) (T : ℝ≥0)
    (hσ : 0 < σ) (hc : 0 < c) (hT : 0 < T)
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (R : ℝ → ℝ → ℝ → ℝ) (hR : IsBddReward R) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (IsEquilibrium x0 σ c T P B R μ ↔
      ∃ f : ℝ → ℝ, (∀ x, 0 < f x) ∧ μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ x, f x = f0 x0 σ T x * Real.exp (Rmu R μ x / (2 * c * σ ^ 2)) / beta x0 σ c T R μ) ∧
    (IsEquilibrium x0 σ c T P B R μ →
      V x0 σ c T P B R μ = 2 * c * σ ^ 2 * Real.log (beta x0 σ c T R μ)) := by sorry

end TerminalRank.Equilibrium
