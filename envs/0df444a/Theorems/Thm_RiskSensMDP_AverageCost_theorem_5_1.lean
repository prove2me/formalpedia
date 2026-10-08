-- Prove2me | Theorems.Thm_RiskSensMDP_AverageCost_theorem_5_1
-- name    : RiskSensMDP.AverageCost.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:12.226035+00:00
-- url     : https://prove2.me/theorems/c5bb49cd-d98f-44e7-a6a9-f40a6f8d1982
-- title:
--   Theorem 5.1 — for a positive Harris recurrent stationary policy, J_π(x) is a limit independent of x and γ, equal to the risk-neutral average cost
-- statement:
--   Let $\pi=(f,f,\dots)$ be a stationary policy whose state process, the Markov chain with kernel $P_f(x,\cdot)=Q(\cdot\mid x,f(x))$, is positive Harris recurrent. Then there is a real number $\rho$ with the following two properties.
--
--   1. For every $\gamma>0$ and every $x\in E$,
--   $$
--   \lim_{n\to\infty}\frac1n\Big(\mathbb E^\pi_x\big[(C^n)^\gamma\big]\Big)^{1/\gamma}=\rho .
--   $$
--   So $J_\pi(x)$ exists as a limit and does not depend on $x$ or $\gamma$.
--   2. For every $x\in E$,
--   $$
--   \lim_{n\to\infty}\frac1n\,\mathbb E^\pi_x[C^n]=\rho .
--   $$
--   So $J_\pi(x)$ coincides with the average cost of a risk-neutral decision maker.
--
--   The theorem says that a decision maker with power utility evaluates a positive Harris recurrent stationary policy exactly as a risk-neutral one does. In the long run, risk sensitivity of this kind has no effect on stationary policies with good recurrence. It is the first step of Theorem 5.2.
--
--   **Formalization Note** "Exists" is rendered as convergence of the defining sequence, of which $J_\pi(x)$ is the $\limsup$. The number $\rho$ is quantified before $\gamma$ and $x$, which encodes the independence. The risk-neutral clause is stated separately even though it is the case $\gamma=1$ of the first. The value of $\rho$ (the integral of $c(x,f(x))$ against the invariant distribution, which appears in the paper's proof) is not part of the statement.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 17, Theorem 5.1

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_RiskSensMDP_AverageCost_Criterion

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

/-- Theorem 5.1 (p. 17): if the state process of the stationary policy `π = (f, f, …)` is positive
Harris recurrent, then `J_π(x)` exists as a limit and does not depend on `x ∈ E` or on `γ > 0`;
the common value is the risk-neutral average cost `lim (1/n) E^π_x[C^n]`. -/
theorem theorem_5_1 {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (f : StationaryRule M)
    (hf : IsPositiveHarrisRecurrent (stateKernel M f)) :
    ∃ ρ : ℝ,
      (∀ γ : ℝ, 0 < γ → ∀ x : E,
        Tendsto (fun n : ℕ => (1 / (n : ℝ)) *
            (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M f.toPolicy x)) ^ (1 / γ)) atTop (nhds ρ)) ∧
      (∀ x : E,
        Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∫ ω, cost M n ω ∂(pathMeasure M f.toPolicy x))
          atTop (nhds ρ)) := by sorry

end RiskSensMDP.AverageCost
