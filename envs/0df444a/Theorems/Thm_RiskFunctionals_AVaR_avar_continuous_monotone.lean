-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_avar_continuous_monotone
-- name    : RiskFunctionals.AVaR.avar_continuous_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:02.786381+00:00
-- url     : https://prove2.me/theorems/617717e2-5244-4adf-83a8-2016df8ebbbe
-- title:
--   Proposition 2.37 — $\alpha\mapsto\mathbb{AV@R}_\alpha(Y)$ is continuous and nondecreasing, with limit $\operatorname{ess\,inf} Y$ at $0$
-- statement:
--   Let $Y$ be an integrable random variable which is not almost surely constant. Then the map
--   $$\alpha \mapsto \mathbb{AV@R}_\alpha(Y), \qquad \alpha\in(0,1],$$
--   is continuous and monotonically increasing, and
--   $$\mathbb{AV@R}_0(Y) = \operatorname{ess\,inf} Y = \lim_{\alpha\downarrow0}\mathbb{AV@R}_\alpha(Y). \tag{2.34}$$
--
--   This is what justifies extending the average value-at-risk to $\alpha=0$ by the essential infimum (2.33).
--
--   **Formalization Note** "Monotonically increasing" is read as nondecreasing: strict increase fails for nonconstant variables with an atom at their minimum (FINDINGS F1). "Nonconstant" is encoded as: there is no constant $c$ with $Y=c$ almost surely. Since $\operatorname{ess\,inf} Y$ may be $-\infty$, the limit is stated in the extended reals, with $\operatorname{ess\,inf}$ computed for $Y$ viewed as an extended-real function; $\mathbb{AV@R}_0(Y)$ is by definition (2.33) this essential infimum. The limit is one-sided, $\alpha\to0$ with $\alpha>0$. $Y$ is assumed measurable.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 54, Proposition 2.37, Eqs. (2.33)–(2.34)

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk

namespace RiskFunctionals.AVaR

open MeasureTheory Filter Topology

/-- Proposition 2.37 (Pflug & Römisch, p. 54): let `Y` be integrable and nonconstant.
The map `α ↦ 𝔸𝕍@ℝ_α(Y)`, `α ∈ (0, 1]`, is continuous and monotonically increasing (read as
nondecreasing), and (2.34) `𝔸𝕍@ℝ₀(Y) = ess inf Y = lim_{α↓0} 𝔸𝕍@ℝ_α(Y)`, the limit taken in the
extended reals since `ess inf Y` may be `−∞`. -/
theorem avar_continuous_monotone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P)
    (hnc : ¬ ∃ c : ℝ, Y =ᵐ[P] fun _ => c) :
    ContinuousOn (fun α : ℝ => averageValueAtRisk P Y α) (Set.Ioc 0 1) ∧
    MonotoneOn (fun α : ℝ => averageValueAtRisk P Y α) (Set.Ioc 0 1) ∧
    Tendsto (fun α : ℝ => ((averageValueAtRisk P Y α : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 (essInf (fun ω => ((Y ω : ℝ) : EReal)) P)) := by sorry

end RiskFunctionals.AVaR
