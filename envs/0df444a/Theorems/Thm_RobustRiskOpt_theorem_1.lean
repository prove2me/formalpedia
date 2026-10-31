-- Prove2me | Theorems.Thm_RobustRiskOpt_theorem_1
-- name    : RobustRiskOpt.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:04.534273+00:00
-- url     : https://prove2.me/theorems/74c16dd4-073a-4a7d-b35e-412db9ce54fa
-- title:
--   Theorem 1, p.13 — $\mathrm{VaR}_p$ is not robust against optimization at $X$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $n\ge1$, and let $X$ be an $n$-dimensional random vector. Let $v:\mathbb R^n\to\mathbb R\cup\{-\infty\}$ and $w:\mathbb R^n\to\mathbb R$ be measurable, let $\gamma:\mathbb R^n\to(0,\infty)$ be measurable, and let $x_0\in\mathbb R$. Let $\mathcal G$ be the admissible set
--
--   $$
--   \mathcal G=\{g\ \text{measurable}:v\le g\le w\ \text{ and }\ \mathbb E[g(X)\gamma(X)]\ge x_0\}.
--   $$
--
--   Let $(\mathcal Z,\pi)$ be $(L^0_n,\pi^W_n)$ or $(L^q_n,\pi^q_n)$ for some $q\in[1,\infty]$, with $X\in\mathcal Z$. Suppose that Assumption G holds: $\mathbb E[\gamma(X)]<\infty$, $\mathcal G\ne\emptyset$, and $\mu_X$ has a positive density on its support, which is a convex subset of $\mathbb R^n$. For $p\in(0,1)$ and $\rho=\mathrm{VaR}_p$, suppose that Assumption V holds:
--
--   $$
--   \operatorname{ess\,sup}(v)<\rho(X;\mathcal G)<\rho(w(X)),
--   $$
--
--   and $\gamma$ is bounded from above.
--
--   Then $\rho=\mathrm{VaR}_p$ is compatible with $(\mathcal G,\mathcal Z,\pi)$ and is **not robust against optimization** at $X$: no optimizer $g_X\in\mathcal G_X(\rho)$ makes $Y\mapsto\rho(g_X(Y))$ $\pi$-continuous at $Y=X$.
--
--   This is the main result of the paper. Although $\mathrm{VaR}_p$ is continuous at positions whose quantile function is continuous at $p$, optimizing it produces a position at which it is discontinuous, even for the strongest metric $\pi^\infty_n$. The set of optimizers may be empty, in which case the statement holds as well.
--
--   Differences from the source:
--   - reading: the budget E[g(X)γ(X)] ⩾ x0 of (7), for which the paper does not say what happens when γg is not integrable → budget is the extended-value expectation E[(γg)₊] − E[(γg)₋] in EReal: the value +∞ is feasible and an undefined difference is ⊥, hence infeasible; reason: the function ĝ = g_X 1_{Aᶜ} + w 1_A of the proof, p.29, must stay in 𝒢 and need not be integrable, since Assumption G does not bound E[γ(X)|w(X)|]; an integrable-only reading breaks that step
--   - generalization: ρ = VaR_p is not robust against optimization at X, where Definition 2 speaks of a compatible ρ → IsCompatible ∧ ¬ RobustAgainstOptimization; reason: the conclusion contains the printed one and records the premise of Definition 2, so that non-robustness cannot hold because of incompatibility; RobustAgainstOptimization does not bundle compatibility
--   - generalization: the probability space (Ω, F, P) is atomless (§2.1, p.5) → no atomlessness hypothesis on Ω; reason: it follows from the density of X in Assumption G, so the printed setting is a special case
--   - generalization: γ is bounded from above (Assumption V) → γ is bounded above μ_X-almost everywhere; reason: the printed pointwise bound implies it; the proof takes all inequalities μ_X-a.s. (p.28)
--   - encoding: μ_X has a positive density on its support, which is a convex subset of ℝⁿ → μ_X and Lebesgue measure restricted to a convex set S are mutually absolutely continuous; reason: the density is positive a.e. on S and zero a.e. off S; a convex set and its closure differ by a null set, so the instances are the same
--   - encoding: v has values in ℝ ∪ {−∞} → v has values in EReal; reason: the value +∞ is excluded by 𝒢 ≠ ∅, since v ⩽ g < +∞ pointwise
--   - encoding: ρ(g(X)) and ρ(X; 𝒢) are extended real numbers → they are EReal-valued, VaR_p being the cast of the real VaR and the infimum being taken in EReal; reason: same values; a real infimum over 𝒢 could be a junk value
--   - encoding: ℝⁿ with the Euclidean norm, n a positive integer → EuclideanSpace ℝ (Fin n) with 0 < n; reason: same space and norm
--   - encoding: π is a real-valued pseudo-metric → π is ℝ≥0∞-valued: levyProkhorovEDist for π^W_n and eLpNorm for π^q_n; reason: same values on the carrier, where the distances are finite
--   - encoding: Y ↦ ρ(g_X(Y)) is π-continuous at Y = X → Tendsto along the filter of π-neighbourhoods of X inside 𝒵; reason: same notion on a pseudo-metric space, and it covers the value +∞
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, Theorem 1 with Assumptions G and V, p.13; Definitions 1–2, p.8

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting
import Definitions.Def_RobustRiskOpt_Admissible
import Definitions.Def_RobustRiskOpt_Model
import Definitions.Def_RobustRiskOpt_Robust
import Definitions.Def_RobustRiskOpt_Assumptions

open MeasureTheory

namespace RobustRiskOpt

/-- Theorem 1, p.13 (Embrechts–Schied–Wang, arXiv:1809.09268v3): for `p ∈ (0, 1)`, under
Assumptions G and V, `ρ = VaR_p` is not robust against optimization at `X` for `(𝒢, 𝒵, π)`.

**Formalization Note** `(𝒵, π)` is the argument `M`, which ranges over `(L⁰ₙ, π^W_n)` and all
`(L^q_n, π^q_n)` with `q ∈ [1, ∞]`. Definition 2 presupposes a compatible `ρ`, so the conclusion
states compatibility and non-robustness separately: `RobustAgainstOptimization` does not contain
compatibility. See the definitions of `budget`, `admissible`, `HasConvexSupportDensity` and
`AssumptionV` for the conventions. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (M : UncertaintyModel)
    (X : Ω → E n) (hX : X ∈ M.carrier P) (v : E n → EReal) (w γ : E n → ℝ) (x₀ : ℝ)
    (hv : Measurable v) (hw : Measurable w) (hγ : Measurable γ) (hγpos : ∀ x, 0 < γ x)
    (hG : AssumptionG P X v w γ x₀) (hV : AssumptionV P p X v w γ x₀) :
    IsCompatible (admissible P X v w γ x₀) (M.carrier P) (M.dist P) (varObj P p) ∧
      ¬ RobustAgainstOptimization (admissible P X v w γ x₀) (M.carrier P) (M.dist P)
        (varObj P p) X := by sorry

end RobustRiskOpt
