-- Prove2me | Theorems.Thm_RiskSensMDP_AverageCost_power_rewriting
-- name    : RiskSensMDP.AverageCost.power_rewriting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:43.98278+00:00
-- url     : https://prove2.me/theorems/805ed46f-b49c-4504-bf20-00773bf2bd3c
-- title:
--   §5.1, p. 17 — for U(y) = y^γ the factor 1/n moves inside: J_σ(x) = lim sup U⁻¹(E^σ_x[U(C^n/n)])
-- statement:
--   Let $\gamma>0$ and $U(y)=y^\gamma$. For every policy $\sigma\in\Pi$, every initial state $x\in E$ and every $n$,
--   $$
--   \frac1n\Big(\mathbb E^\sigma_x\big[(C^n)^\gamma\big]\Big)^{1/\gamma}=\Big(\mathbb E^\sigma_x\Big[\Big(\frac{C^n}{n}\Big)^\gamma\Big]\Big)^{1/\gamma},
--   $$
--   and consequently
--   $$
--   J_\sigma(x)=\limsup_{n\to\infty}\frac1n U^{-1}\Big(\mathbb E^\sigma_x\big[U(C^n)\big]\Big)=\limsup_{n\to\infty}U^{-1}\Big(\mathbb E^\sigma_x\Big[U\Big(\frac{C^n}{n}\Big)\Big]\Big).
--   $$
--
--   Homogeneity of the power utility thus turns the risk-sensitive average cost into the certainty equivalent of the empirical average cost $C^n/n$. The paper derives Theorem 5.1 from this form.
--
--   **Formalization Note** At $n=0$ both sides equal $0$, because Lean sets $1/0=0$ and $0/0=0$. The identity is stated for every $n$, together with the equality of the two limits superior.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 17, §5.1, unnumbered display

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_RiskSensMDP_AverageCost_Criterion

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

/-- §5.1, p. 17 (unnumbered display): for `U(y) = y^γ` with `γ > 0`,
`(1/n) U⁻¹(E^σ_x[U(C^n)]) = U⁻¹(E^σ_x[U(C^n/n)])` for every `n`, hence
`J_σ(x) = limsup (1/n) U⁻¹(E^σ_x[U(C^n)]) = limsup U⁻¹(E^σ_x[U(C^n/n)])`. -/
theorem power_rewriting {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (γ : ℝ) (hγ : 0 < γ) (σ : Policy M) (x : E) :
    (∀ n : ℕ, (1 / (n : ℝ)) * (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ) =
        (∫ ω, (cost M n ω / n) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ)) ∧
    powerAvgCost M γ σ x =
      limsup (fun n : ℕ => (∫ ω, (cost M n ω / n) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ)) atTop := by sorry

end RiskSensMDP.AverageCost
