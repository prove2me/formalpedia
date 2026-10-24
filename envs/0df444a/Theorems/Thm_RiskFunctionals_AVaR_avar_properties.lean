-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_avar_properties
-- name    : RiskFunctionals.AVaR.avar_properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:08.222649+00:00
-- url     : https://prove2.me/theorems/8e107445-72e4-4fcf-8e71-a887d9c4b107
-- title:
--   Proposition 2.35 (i)–(vii) — properties of the average value-at-risk
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $0<\alpha\le1$. On integrable random variables, the average value-at-risk $\mathbb{AV@R}_\alpha$ is
--
--   1. **translation-equivariant** (A1): $\mathbb{AV@R}_\alpha(Y+c)=\mathbb{AV@R}_\alpha(Y)+c$ for every constant $c$;
--   2. **concave** (A2): $\mathbb{AV@R}_\alpha(\lambda Y^{(1)}+(1-\lambda)Y^{(2)})\ge\lambda\,\mathbb{AV@R}_\alpha(Y^{(1)})+(1-\lambda)\,\mathbb{AV@R}_\alpha(Y^{(2)})$ for $0\le\lambda\le1$;
--   3. **isotonic with respect to second-order stochastic dominance** (A3.2): $Y^{(1)}\prec_{SSD}Y^{(2)}$ implies $\mathbb{AV@R}_\alpha(Y^{(1)})\le\mathbb{AV@R}_\alpha(Y^{(2)})$; and in particular
--   $$\mathbb{AV@R}_\alpha(Y) \le \mathbb{AV@R}_\alpha\big(\mathbb E(Y\mid\mathcal F_1)\big) \tag{2.31}$$
--   for every sub-$\sigma$-algebra $\mathcal F_1\subseteq\mathcal F$;
--   4. **positively homogeneous** (A4): $\mathbb{AV@R}_\alpha(\lambda Y)=\lambda\,\mathbb{AV@R}_\alpha(Y)$ for $\lambda\ge0$;
--   5. **strict** (A5): the average value-at-risk deviation $\mathbb{AV@R}\mathbb D_\alpha(Y)=\mathbb E Y-\mathbb{AV@R}_\alpha(Y)$ is nonnegative;
--   6. **Lipschitz continuous on $L_1$**: there is a constant $L$ with $|\mathbb{AV@R}_\alpha(Y^{(1)})-\mathbb{AV@R}_\alpha(Y^{(2)})|\le L\,\mathbb E|Y^{(1)}-Y^{(2)}|$;
--   7. **comonotone additive**: $\mathbb{AV@R}_\alpha(Y^{(1)}+Y^{(2)})=\mathbb{AV@R}_\alpha(Y^{(1)})+\mathbb{AV@R}_\alpha(Y^{(2)})$ whenever $Y^{(1)}$, $Y^{(2)}$ are comonotone.
--
--   Properties (A1)–(A3) make $\mathbb{AV@R}_\alpha$ an acceptability functional in the book's sense; with (A4) and (A5) it is a positively homogeneous, strict one.
--
--   **Formalization Note** All random variables are measurable and integrable. $\prec_{SSD}$ is defined through nondecreasing concave utilities (Definition 1.10), applied to the laws; comonotone means that the joint distribution function is $\min(G_1(u),G_2(v))$ (Definition 1.4, (1.11)). $\mathbb E(Y\mid\mathcal F_1)$ is Mathlib's conditional expectation. The Lipschitz constant is existential, as in the statement; the book's proof gives $L=1/\alpha$. Part (viii) of the proposition, compound convexity, is not included: it needs Definition 2.11, which is outside this chapter.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 53, Proposition 2.35 (i)–(vii)

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_AVaR_Orders

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- Proposition 2.35 (i)–(vii) (Pflug & Römisch, p. 53), on integrable random variables of
`(Ω, ℱ, P)`, for fixed `0 < α ≤ 1`: `𝔸𝕍@ℝ_α` is
(i) translation-equivariant (A1): `𝔸𝕍@ℝ_α(Y + c) = 𝔸𝕍@ℝ_α(Y) + c`;
(ii) concave (A2);
(iii) isotonic w.r.t. SSD (A3.2), and `𝔸𝕍@ℝ_α(Y) ≤ 𝔸𝕍@ℝ_α(𝔼(Y|ℱ₁))` (2.31) for every
  σ-algebra `ℱ₁ ⊆ ℱ`;
(iv) positively homogeneous (A4): `𝔸𝕍@ℝ_α(λY) = λ 𝔸𝕍@ℝ_α(Y)`, `λ ≥ 0`;
(v) strict (A5): `𝔸𝕍@ℝ𝔻_α(Y) ≥ 0`;
(vi) Lipschitz continuous on `L₁`;
(vii) comonotone additive.
Part (viii) (compound convexity) is not stated here. -/
theorem avar_properties {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    -- (i) translation equivariance (A1)
    (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P → ∀ c : ℝ,
      averageValueAtRisk P (fun ω => Y ω + c) α = averageValueAtRisk P Y α + c) ∧
    -- (ii) concavity (A2)
    (∀ Y₁ Y₂ : Ω → ℝ, Measurable Y₁ → Integrable Y₁ P → Measurable Y₂ → Integrable Y₂ P →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        t * averageValueAtRisk P Y₁ α + (1 - t) * averageValueAtRisk P Y₂ α ≤
          averageValueAtRisk P (fun ω => t * Y₁ ω + (1 - t) * Y₂ ω) α) ∧
    -- (iii) isotonicity w.r.t. SSD (A3.2) ...
    (∀ Y₁ Y₂ : Ω → ℝ, Measurable Y₁ → Integrable Y₁ P → Measurable Y₂ → Integrable Y₂ P →
      SSD (P.map Y₁) (P.map Y₂) → averageValueAtRisk P Y₁ α ≤ averageValueAtRisk P Y₂ α) ∧
    -- ... and (2.31)
    (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P → ∀ m : MeasurableSpace Ω, m ≤ mΩ →
      @averageValueAtRisk Ω mΩ P Y α ≤ @averageValueAtRisk Ω mΩ P (P[Y|m]) α) ∧
    -- (iv) positive homogeneity (A4)
    (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P → ∀ t : ℝ, 0 ≤ t →
      averageValueAtRisk P (fun ω => t * Y ω) α = t * averageValueAtRisk P Y α) ∧
    -- (v) strictness (A5)
    (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P → 0 ≤ avarDeviation P Y α) ∧
    -- (vi) Lipschitz continuity on L₁
    (∃ L : ℝ, ∀ Y₁ Y₂ : Ω → ℝ, Measurable Y₁ → Integrable Y₁ P → Measurable Y₂ →
      Integrable Y₂ P →
        |averageValueAtRisk P Y₁ α - averageValueAtRisk P Y₂ α| ≤
          L * ∫ ω, |Y₁ ω - Y₂ ω| ∂P) ∧
    -- (vii) comonotone additivity
    (∀ Y₁ Y₂ : Ω → ℝ, Measurable Y₁ → Integrable Y₁ P → Measurable Y₂ → Integrable Y₂ P →
      Comonotone P Y₁ Y₂ →
        averageValueAtRisk P (fun ω => Y₁ ω + Y₂ ω) α =
          averageValueAtRisk P Y₁ α + averageValueAtRisk P Y₂ α) := by sorry

end RiskFunctionals.AVaR
