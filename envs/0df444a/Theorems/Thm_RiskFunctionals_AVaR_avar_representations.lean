-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_avar_representations
-- name    : RiskFunctionals.AVaR.avar_representations
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:01.899555+00:00
-- url     : https://prove2.me/theorems/f785937a-14bd-48c4-a280-232335b89ec4
-- title:
--   Theorem 2.34 — five representations of the average value-at-risk
-- statement:
--   Let $Y$ be an integrable random variable on $(\Omega,\mathcal F,\mathbb P)$ with distribution function $G$ and quantile function $G^{-1}$, let $0<\alpha\le1$, and let $\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du$. Write $[y]^-=-\min(y,0)$, $\alpha^+_G=\inf\{G(u):G(u)\ge\alpha\}$ and $\alpha^-_G=\sup\{G(u):G(u)<\alpha\}$.
--
--   1. (Rockafellar–Uryasev representation.)
--   $$\mathbb{AV@R}_\alpha(Y) = \max\Big\{x-\frac1\alpha\,\mathbb E\big([Y-x]^-\big) : x\in\mathbb R\Big\}, \tag{2.19}$$
--   and the maximum is attained.
--   2. (Dual representation.)
--   $$\mathbb{AV@R}_\alpha(Y) = \min\Big\{\mathbb E(YZ) : \mathbb E Z=1,\ 0\le Z\le \tfrac1\alpha\Big\}, \tag{2.20}$$
--   the minimum over random variables $Z$ on $(\Omega,\mathcal F,\mathbb P)$, and the minimum is attained.
--
--   If moreover $G^{-1}(\alpha)$ is finite, then:
--
--   3. $$\mathbb{AV@R}_\alpha(Y) = G^{-1}(\alpha) - \frac1\alpha\,\mathbb E\big([Y-G^{-1}(\alpha)]^-\big) = G^{-1}(\alpha) - \frac1\alpha\int_{-\infty}^{G^{-1}(\alpha)}\big(G^{-1}(\alpha)-u\big)\,dG(u). \tag{2.21}$$
--   4. (Conditional tail expectation, strict tail.)
--   $$\mathbb{AV@R}_\alpha(Y) = \frac{\alpha^-_G}{\alpha}\,\mathbb E\big[Y \mid Y<G^{-1}(\alpha)\big] + \frac{\alpha-\alpha^-_G}{\alpha}\,G^{-1}(\alpha). \tag{2.22}$$
--   5. (Conditional tail expectation, closed tail.)
--   $$\mathbb{AV@R}_\alpha(Y) = \frac{\alpha^+_G}{\alpha}\,\mathbb E\big[Y \mid Y\le G^{-1}(\alpha)\big] - \frac{\alpha^+_G-\alpha}{\alpha}\,G^{-1}(\alpha). \tag{2.23}$$
--
--   The theorem holds for distributions with atoms, which is its point: the naive formula "average of $Y$ below its $\alpha$-quantile" is wrong when $G$ jumps at $G^{-1}(\alpha)$, and (2.22), (2.23) give the corrections.
--
--   **Formalization Note** Parts 1 and 2 are stated, as printed, for every $0<\alpha\le1$. Parts 3–5 use $G^{-1}(\alpha)$ as a real number, and the book's statement of them presupposes it; they carry the hypothesis "$G^{-1}(\alpha)$ finite", i.e. $G(u)\ge\alpha$ for some $u$, which is automatic for $\alpha<1$ and at $\alpha=1$ says that $Y$ is essentially bounded above. At $\alpha=1$ with $Y$ not essentially bounded above, the attainment claim of part 1 fails (FINDINGS F2); the statement here keeps it as printed, and the variant `RiskFunctionals.AVaR.avar_representations_corrected` states it under the finiteness hypothesis. In part 2, $Z$ ranges over measurable real functions with $\int Z\,d\mathbb P=1$ and $0\le Z\le1/\alpha$ almost surely. $\mathbb E[Y\mid A]$ is the elementary conditional expectation, the integral of $Y$ against the conditional probability $\mathbb P(\,\cdot\mid A)$; when $\mathbb P(A)=0$ this conditional measure is the zero measure, and then the coefficient $\alpha^-_G$ (resp. $\alpha^+_G$) in front of it equals $\mathbb P(A)=0$ as well, so the term is $0$, as it should be. The second expression in (2.21) is an integral against the law of $Y$ over $(-\infty, G^{-1}(\alpha)]$; the book prints its lower limit as $\infty$, a typo for $-\infty$. The book's remark after (2.20) that $\mathbb{AV@R}_\alpha$ is concave and u.s.c. is not part of this statement; concavity and $L_1$-Lipschitz continuity are Proposition 2.35. $Y$ is assumed measurable.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 49–50, Theorem 2.34

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk

namespace RiskFunctionals.AVaR

open MeasureTheory ProbabilityTheory

/-- Theorem 2.34 (Pflug & Römisch, pp. 49–50), for an integrable random variable `Y` with
distribution function `G` and `0 < α ≤ 1`; `[y]⁻ = −min(y, 0)`.
(i) (2.19) `𝔸𝕍@ℝ_α(Y) = max {x − (1/α) 𝔼([Y − x]⁻) : x ∈ ℝ}`, the maximum attained;
(ii) (2.20) `𝔸𝕍@ℝ_α(Y) = min {𝔼(Y Z) : 𝔼Z = 1, 0 ≤ Z ≤ 1/α}`, the minimum attained;
(iii) (2.21) `𝔸𝕍@ℝ_α(Y) = G⁻¹(α) − (1/α) 𝔼([Y − G⁻¹(α)]⁻)
  = G⁻¹(α) − (1/α) ∫_{−∞}^{G⁻¹(α)} (G⁻¹(α) − u) dG(u)` (the book prints the lower limit as `∞`);
(iv) (2.22) `𝔸𝕍@ℝ_α(Y) = (α⁻_G/α) 𝔼[Y | Y < G⁻¹(α)] + ((α − α⁻_G)/α) G⁻¹(α)`;
(v) (2.23) `𝔸𝕍@ℝ_α(Y) = (α⁺_G/α) 𝔼[Y | Y ≤ G⁻¹(α)] − ((α⁺_G − α)/α) G⁻¹(α)`.
Parts (iii), (iv), (v) involve `G⁻¹(α)` as a real number and are stated when it is finite,
i.e. `G(u) ≥ α` for some `u` (automatic for `α < 1`). Part (i) is stated as printed, for every
`0 < α ≤ 1` (see finding F2 on `α = 1`). `𝔼[Y | A]` is the elementary conditional
expectation, the integral of `Y` against `P[|A]`. -/
theorem avar_representations {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    -- (i) (2.19), with attainment
    IsGreatest {v : ℝ | ∃ x : ℝ, v = x - (1 / α) * ∫ ω, -min (Y ω - x) 0 ∂P}
      (averageValueAtRisk P Y α) ∧
    -- (ii) (2.20), with attainment
    IsLeast {v : ℝ | ∃ Z : Ω → ℝ, Measurable Z ∧ ∫ ω, Z ω ∂P = 1 ∧
        (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ 1 / α) ∧ v = ∫ ω, Y ω * Z ω ∂P}
      (averageValueAtRisk P Y α) ∧
    ((∃ u : ℝ, α ≤ distributionFunction (P.map Y) u) →
      -- (iii) (2.21), both lines
      (averageValueAtRisk P Y α = quantileFunction (P.map Y) α
          - (1 / α) * ∫ ω, -min (Y ω - quantileFunction (P.map Y) α) 0 ∂P ∧
        averageValueAtRisk P Y α = quantileFunction (P.map Y) α
          - (1 / α) * ∫ u in Set.Iic (quantileFunction (P.map Y) α),
              (quantileFunction (P.map Y) α - u) ∂(P.map Y)) ∧
      -- (iv) (2.22)
      averageValueAtRisk P Y α =
        alphaMinus (P.map Y) α / α *
            ∫ ω, Y ω ∂(P[|{ω | Y ω < quantileFunction (P.map Y) α}])
          + (α - alphaMinus (P.map Y) α) / α * quantileFunction (P.map Y) α ∧
      -- (v) (2.23)
      averageValueAtRisk P Y α =
        alphaPlus (P.map Y) α / α *
            ∫ ω, Y ω ∂(P[|{ω | Y ω ≤ quantileFunction (P.map Y) α}])
          - (alphaPlus (P.map Y) α - α) / α * quantileFunction (P.map Y) α) := by sorry

end RiskFunctionals.AVaR
