-- Prove2me | Theorems.Thm_RiskSensMDP_AverageCost_jensen_step
-- name    : RiskSensMDP.AverageCost.jensen_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:46.310719+00:00
-- url     : https://prove2.me/theorems/700eb9db-a2f4-4e13-b2d9-61eb48a3278e
-- title:
--   §5.1, proof of Theorem 5.2, p. 17 — lim sup E^σ_x[C^n/n] ≤ J_σ(x) for γ ≥ 1 (Jensen)
-- statement:
--   Let $\gamma\ge1$ and $U(y)=y^\gamma$. For every policy $\sigma\in\Pi$ and every initial state $x\in E$, the risk-neutral average cost is at most the risk-sensitive one:
--   $$
--   \rho_\sigma(x)=\limsup_{n\to\infty}\mathbb E^\sigma_x\Big[\frac{C^n}{n}\Big]\le\limsup_{n\to\infty}U^{-1}\Big(\mathbb E^\sigma_x\Big[U\Big(\frac{C^n}{n}\Big)\Big]\Big)=J_\sigma(x).
--   $$
--
--   This is the comparison step of the paper's proof of Theorem 5.2. For a convex utility the certainty-equivalent cost is never below the expected cost, for every policy, including history-dependent ones.
--
--   **Formalization Note** Both sides are the limits superior defined in `Criterion`: $\rho_\sigma(x)=\limsup\frac1n\mathbb E^\sigma_x[C^n]$ and $J_\sigma(x)=\limsup\frac1n(\mathbb E^\sigma_x[(C^n)^\gamma])^{1/\gamma}$. Their equality with the displayed forms is linearity of expectation and the preceding milestone.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 17, §5.1, proof of Theorem 5.2, last display

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_RiskSensMDP_AverageCost_Criterion

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

/-- §5.1, proof of Theorem 5.2, p. 17: for `γ ≥ 1` (convex `U(y) = y^γ`), Jensen's inequality gives
`limsup_{n → ∞} E^σ_x[C^n/n] ≤ limsup_{n → ∞} U⁻¹(E^σ_x[U(C^n/n)]) = J_σ(x)` for every policy
`σ ∈ Π` and every `x ∈ E`. -/
theorem jensen_step {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (γ : ℝ) (hγ : 1 ≤ γ) (σ : Policy M) (x : E) :
    riskNeutralAvgCost M σ x ≤ powerAvgCost M γ σ x := by sorry

end RiskSensMDP.AverageCost
