-- Prove2me | Theorems.Thm_RiskFunctionals_StochDominance_dominance_characterizations
-- name    : RiskFunctionals.StochDominance.dominance_characterizations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:36.58902+00:00
-- url     : https://prove2.me/theorems/48ecba72-5b36-4794-8f37-82f0c2619a96
-- title:
--   Theorem 1.13 — six characterizations of first-order, second-order and concave dominance
-- statement:
--   Let $G_1$, $G_2$ be distribution functions on $\mathbb R$ with quantile functions $G_1^{-1}$, $G_2^{-1}$. The orders $\prec_{FSD}$, $\prec_{SSD}$, $\prec_{CCD}$ are those of Definition 1.10 (comparison of $\int U\,dG_1$ and $\int U\,dG_2$ over nondecreasing, nondecreasing concave, resp. concave utilities $U$ for which the integrals exist). When $G_i$ has a first moment, $\mathcal G_i$ is its integrated distribution function, $\mathcal G_i^{[-1]}$ its integrated quantile function and $\mathbb E\{G_i\}$ its mean. Then:
--
--   1. $G_1 \prec_{FSD} G_2$ is equivalent to $G_1(u) \ge G_2(u)$ for all $u\in\mathbb R$.
--   2. $G_1 \prec_{FSD} G_2$ is also equivalent to $G_1^{-1}(p) \le G_2^{-1}(p)$ for all $p\in(0,1)$.
--
--   If moreover both $G_1$ and $G_2$ have a first moment:
--
--   3. $G_1 \prec_{CCD} G_2$ is equivalent to $G_1 \prec_{SSD} G_2$ together with $\mathbb E\{G_1\} = \mathbb E\{G_2\}$.
--   4. $G_1 \prec_{CCD} G_2$ is also equivalent to the existence of a Markov kernel $K$ from $\mathbb R$ to $\mathbb R$, with $K(\cdot\,|\,v)$ the distribution function of the probability measure $K(v)$, such that
--   $$G_1(u) = \int K(u\,|\,v)\,dG_2(v)\ \text{ for all } u \qquad\text{and}\qquad \int u\,dK(u\,|\,v) = v\ \text{ for all } v.$$
--   5. $G_1 \prec_{SSD} G_2$ is equivalent to $\mathcal G_1(u) \ge \mathcal G_2(u)$ for all $u\in\mathbb R$.
--   6. $G_1 \prec_{SSD} G_2$ is also equivalent to $\mathcal G_1^{[-1]}(p) \le \mathcal G_2^{[-1]}(p)$ for all $p\in(0,1)$.
--
--   In the book's profit convention these are the working forms of the dominance relations: (1)–(2) compare distribution and quantile functions pointwise, (5)–(6) compare their integrals, (3) separates concave dominance into second-order dominance plus equality of means, and (4) is Strassen's representation of concave dominance as a mean-preserving spread.
--
--   **Formalization Note** The distributions are probability measures $\mu_1,\mu_2$ on $\mathbb R$, not random variables on a common space. The conclusion is the conjunction of the six parts; the first-moment hypotheses (integrability of the identity under $\mu_1$ and $\mu_2$) are attached to parts 3–6, where the book's $\mathbb E\{G_i\}$, $\mathcal G_i$, $\mathcal G_i^{[-1]}$ and the kernel's mean occur, and not to parts 1–2. In part 4, the kernel is a Mathlib Markov kernel `Kernel ℝ ℝ`; "$\int u\,dK(u|v) = v$ for all $v$" is stated for every $v$, as printed, and includes the integrability of the identity under $K(v)$, which is what makes that integral a real number. Quantile comparisons are over the open interval $(0,1)$, as printed, so the junk value of the real quantile function at $p=1$ never enters.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 16, Theorem 1.13

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction
import Definitions.Def_RiskFunctionals_StochDominance_IntegratedFunctions
import Definitions.Def_RiskFunctionals_StochDominance_Dominance

namespace RiskFunctionals.StochDominance

open MeasureTheory ProbabilityTheory

/-- Theorem 1.13 (Pflug & Römisch, p. 16), for distributions `G₁`, `G₂` given as probability
measures `μ₁`, `μ₂` on `ℝ`:
(i) `G₁ ≺_FSD G₂` iff `G₁(u) ≥ G₂(u)` for all `u`;
(ii) `G₁ ≺_FSD G₂` iff `G₁⁻¹(p) ≤ G₂⁻¹(p)` for all `p ∈ (0,1)`;
and, when both have a first moment,
(iii) `G₁ ≺_CCD G₂` iff `G₁ ≺_SSD G₂` and `𝔼{G₁} = 𝔼{G₂}`;
(iv) `G₁ ≺_CCD G₂` iff there is a Markov kernel `K` with `G₁(u) = ∫ K(u|v) dG₂(v)` for all `u`
and `∫ u dK(u|v) = v` for all `v`;
(v) `G₁ ≺_SSD G₂` iff `𝒢₁(u) ≥ 𝒢₂(u)` for all `u`;
(vi) `G₁ ≺_SSD G₂` iff `𝒢₁^{[-1]}(p) ≤ 𝒢₂^{[-1]}(p)` for all `p ∈ (0,1)`. -/
theorem dominance_characterizations (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    (FSD μ₁ μ₂ ↔ ∀ u : ℝ, distributionFunction μ₂ u ≤ distributionFunction μ₁ u) ∧
    (FSD μ₁ μ₂ ↔ ∀ p ∈ Set.Ioo (0 : ℝ) 1, quantileFunction μ₁ p ≤ quantileFunction μ₂ p) ∧
    (Integrable (fun v : ℝ => v) μ₁ → Integrable (fun v : ℝ => v) μ₂ →
      (CCD μ₁ μ₂ ↔ SSD μ₁ μ₂ ∧ ∫ v, v ∂μ₁ = ∫ v, v ∂μ₂)) ∧
    (Integrable (fun v : ℝ => v) μ₁ → Integrable (fun v : ℝ => v) μ₂ →
      (CCD μ₁ μ₂ ↔ ∃ K : Kernel ℝ ℝ, IsMarkovKernel K ∧
        (∀ u : ℝ, distributionFunction μ₁ u = ∫ v, distributionFunction (K v) u ∂μ₂) ∧
        (∀ v : ℝ, Integrable (fun u : ℝ => u) (K v) ∧ ∫ u, u ∂(K v) = v))) ∧
    (Integrable (fun v : ℝ => v) μ₁ → Integrable (fun v : ℝ => v) μ₂ →
      (SSD μ₁ μ₂ ↔ ∀ u : ℝ,
        integratedDistributionFunction μ₂ u ≤ integratedDistributionFunction μ₁ u)) ∧
    (Integrable (fun v : ℝ => v) μ₁ → Integrable (fun v : ℝ => v) μ₂ →
      (SSD μ₁ μ₂ ↔ ∀ p ∈ Set.Ioo (0 : ℝ) 1,
        integratedQuantileFunction μ₁ p ≤ integratedQuantileFunction μ₂ p)) := by sorry

end RiskFunctionals.StochDominance
