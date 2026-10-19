-- Prove2me | Theorems.Thm_TerminalRank_Equilibrium_proposition_2_1
-- name    : TerminalRank.Equilibrium.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:00.36306+00:00
-- url     : https://prove2.me/theorems/01f29d84-c84b-4799-b166-55e491bb8711
-- title:
--   Proposition 2.1, p. 5, for R ∈ ℛ_b — the best response has density f0·exp(R_µ̃/2cσ²)/β(µ̃) and V(R, µ̃) = 2cσ² ln β(µ̃)
-- statement:
--   Under the standing data ($T>0$, $c>0$, $\sigma>0$, $x_0$, a Brownian motion $B$ under $P$, $X_T=x_0+\sigma B_T$), let $R\in\mathcal R_b$ and $\tilde\mu\in\mathcal P(\mathbb R)$ have a finite first moment, and set
--   $$\beta(\tilde\mu)=\int_{\mathbb R}f_0(y)\exp\Big(\frac{R_{\tilde\mu}(y)}{2c\sigma^2}\Big)dy .$$
--   Then:
--   1. the optimal value is $V(R,\tilde\mu)=2c\sigma^2\ln\beta(\tilde\mu)$;
--   2. an optimal control $Q^*\in\mathcal Q$ exists;
--   3. every optimal control has terminal law $\mu^*$ with density
--   $$f_{\mu^*}(x)=\frac{1}{\beta(\tilde\mu)}f_0(x)\exp\Big(\frac{R_{\tilde\mu}(x)}{2c\sigma^2}\Big). \tag{2.9}$$
--
--   This is the best response of a single player to the population law $\tilde\mu$: a Gibbs tilt of the uncontrolled terminal Gaussian law. The equilibrium analysis of Section 3 is a fixed point of this map.
--
--   **Formalization Note.** The paper states the proposition for $R\in\mathcal R$ under $\beta(\tilde\mu)<\infty$; for bounded rewards this condition always holds, and the statement is given for $R\in\mathcal R_b$. The finite-mean condition makes $R_{\tilde\mu}$ defined. "The optimal terminal distribution" is read as existence of an optimizer together with the identification of the terminal law of every optimizer.
-- source:
--   Bayraktar & Zhang, Terminal Ranking Games, arXiv:1906.09628v2, p. 5, Proposition 2.1, (2.7), (2.9)

import Mathlib
import Definitions.Def_TerminalRank_Equilibrium_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TerminalRank.Equilibrium

/-- Proposition 2.1, p. 5 (Bayraktar–Zhang, arXiv:1906.09628v2), specialized to `R ∈ ℛ_b`
(where `β(µ̃) < ∞` holds automatically) and population laws with finite mean: the optimal value is
`V(R, µ̃) = 2cσ² ln β(µ̃)`, an optimal
control exists, and every optimal control has terminal law with density
`f_{µ*}(x) = f0(x) exp(R_µ̃(x)/(2cσ²)) / β(µ̃)` (2.9). -/
theorem proposition_2_1 {Ω : Type*} [MeasurableSpace Ω] (x0 σ c : ℝ) (T : ℝ≥0)
    (hσ : 0 < σ) (hc : 0 < c) (hT : 0 < T)
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (R : ℝ → ℝ → ℝ → ℝ) (hR : IsBddReward R) (μt : Measure ℝ) [IsProbabilityMeasure μt]
    (hμt : Integrable (fun y : ℝ => y) μt) :
    V x0 σ c T P B R μt = 2 * c * σ ^ 2 * Real.log (beta x0 σ c T R μt) ∧
      (∃ Q : Measure Ω, IsOptimal x0 σ c T P B R μt Q) ∧
      ∀ Q : Measure Ω, IsOptimal x0 σ c T P B R μt Q →
        Q.map (XT x0 σ B T) = volume.withDensity (fun x => ENNReal.ofReal
          (f0 x0 σ T x * Real.exp (Rmu R μt x / (2 * c * σ ^ 2)) / beta x0 σ c T R μt)) := by sorry

end TerminalRank.Equilibrium
