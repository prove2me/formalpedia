-- Prove2me | Theorems.Thm_RiskFunctionals_Distortion_choquet_representation
-- name    : RiskFunctionals.Distortion.choquet_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:14.443173+00:00
-- url     : https://prove2.me/theorems/8d51009d-a35f-431e-90dd-9231b95ab3a2
-- title:
--   Proposition 2.64 — Choquet representation $\mathcal A_H\{G\}=\int_0^1\mathbb{AV@R}_\alpha\{G\}\,dM(\alpha)$ of concave distortion functionals, and its converse
-- statement:
--   Let $\mathcal A_H\{G\}=\int_0^1G^{-1}(p)\,dH(p)$ be the distortion functional of a distortion function $H$ (bounded, right continuous, increasing on $[0,1]$), defined for distributions $G$ in $\mathcal G_H$, and let $\mathbb{AV@R}_\alpha\{G\}=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du$ for $0<\alpha\le1$.
--
--   1. Suppose that $H$ is concave, i.e. $H(p)=\int_0^p h(\alpha)\,d\alpha$ with a nonincreasing $h$. Then there is a monotonically increasing $M$ on $[0,1]$ with $M(0)=0$ and $M(1)=H(1)$ such that $\alpha\mapsto\mathbb{AV@R}_\alpha\{G\}$ is $dM$-integrable on $[0,1]$ and the **Choquet representation**
--   $$\mathcal A_H\{G\}=\int_0^1\mathbb{AV@R}_\alpha\{G\}\,dM(\alpha) \tag{2.66}$$
--   holds for every $G\in\mathcal G_H$.
--   2. Conversely, every comonotone additive functional having a Choquet representation is a distortion functional: if $\mathcal A$ is additive on comonotone pairs and $\mathcal A(Y)=\int_0^1\mathbb{AV@R}_\alpha(Y)\,dM(\alpha)$ for an increasing $M$ with $M(0)=0$, then there is a distortion function $H$ with $G_Y\in\mathcal G_H$ and $\mathcal A(Y)=\mathcal A_H(Y)$ for every $Y$ on which the representation holds.
--
--   Concave distortion functionals are thus exactly the mixtures of average values-at-risk; their concavity, isotonicity with respect to second-order dominance and comonotone additivity follow from this representation.
--
--   **Formalization Note** $H$ and $M$ are Mathlib `StieltjesFunction`s (monotone and right continuous on $\mathbb R$; for $M$ this is the right continuous normalisation of an increasing function, which defines the same Stieltjes measure). $M$ is required to vanish on $(-\infty,0]$, so $dM$ has no atom at $0$ ($M(0)=0$), and $\int_0^1\cdots dM$ is the integral over $[0,1]$ against $dM$. In part 1, $h$ is nonincreasing on $(0,1]$ and Lebesgue integrable there (the book allows $h(0+)=+\infty$), $H(p)=\int_0^ph$ on $[0,1]$, and $M$ is chosen before $G$: one $M$ serves every $G\in\mathcal G_H$. In part 2, the functional $\mathcal A$ acts on random variables of a probability space $(\Omega,\mathcal F,\mathbb P)$; the representation, the comonotone additivity and the conclusion are stated on the measurable integrable $Y$ for which $\alpha\mapsto\mathbb{AV@R}_\alpha(Y)$ is $dM$ integrable on $[0,1]$. $\mathcal G_H$ is as in the definition file (including $H(0)=0$).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 85, Proposition 2.64

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional
import Definitions.Def_RiskFunctionals_Distortion_Orders

namespace RiskFunctionals.Distortion

open MeasureTheory

/-- Proposition 2.64 (Pflug & Römisch, p. 85), Choquet representation for distortion
functionals.
(1) Suppose `H` is concave, i.e. `H(p) = ∫₀^p h(α) dα` with a nonincreasing `h`. Then there is a
monotonically increasing `M` with `M(0) = 0`, `M(1) = H(1)` such that, for every distribution
`G ∈ 𝒢_H`, `α ↦ 𝔸𝕍@ℝ_α{G}` is `dM` integrable on `[0, 1]` and
`𝒜_H{G} = ∫₀¹ 𝔸𝕍@ℝ_α{G} dM(α)` (2.66).
(2) Conversely, every comonotone additive functional `𝒜` having a Choquet representation
`𝒜(Y) = ∫₀¹ 𝔸𝕍@ℝ_α(Y) dM(α)` is a distortion functional: there is `H` with `G_Y ∈ 𝒢_H` and
`𝒜(Y) = 𝒜_H(Y)` for every `Y` on which the representation is stated.
`M` is a `StieltjesFunction` (right continuous normalisation of an increasing function),
extended by `0` on `(−∞, 0]`, so `dM` has no atom at `0`; the integral `∫₀¹ … dM` is over
`[0, 1]`. In (2) the representation is stated on the random variables `Y` of `(Ω, ℱ, P)` that are
measurable, integrable and for which `α ↦ 𝔸𝕍@ℝ_α(Y)` is `dM` integrable on `[0, 1]`. -/
theorem choquet_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    -- (1) H concave ⇒ Choquet representation (2.66)
    (∀ (H : StieltjesFunction ℝ) (h : ℝ → ℝ), AntitoneOn h (Set.Ioc 0 1) →
      IntegrableOn h (Set.Ioc 0 1) →
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = ∫ α in (0 : ℝ)..p, h α) →
      ∃ M : StieltjesFunction ℝ, (∀ x ≤ 0, M x = 0) ∧ M 1 = H 1 ∧
        ∀ μ : Measure ℝ, IsProbabilityMeasure μ → InDistortionDomain H μ →
          IntegrableOn (fun α => averageValueAtRisk μ α) (Set.Icc 0 1) M.measure ∧
          distortionFunctional H μ =
            ∫ α in Set.Icc (0 : ℝ) 1, averageValueAtRisk μ α ∂M.measure) ∧
    -- (2) comonotone additive + Choquet representation ⇒ distortion functional
    (∀ (A : (Ω → ℝ) → ℝ) (M : StieltjesFunction ℝ), (∀ x ≤ 0, M x = 0) →
      (∀ Y₁ Y₂ : Ω → ℝ,
        Measurable Y₁ → Integrable Y₁ P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y₁) α) (Set.Icc 0 1) M.measure →
        Measurable Y₂ → Integrable Y₂ P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y₂) α) (Set.Icc 0 1) M.measure →
        Comonotone P Y₁ Y₂ → A (fun ω => Y₁ ω + Y₂ ω) = A Y₁ + A Y₂) →
      (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y) α) (Set.Icc 0 1) M.measure →
        A Y = ∫ α in Set.Icc (0 : ℝ) 1, averageValueAtRisk (P.map Y) α ∂M.measure) →
      ∃ H : StieltjesFunction ℝ, ∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y) α) (Set.Icc 0 1) M.measure →
          InDistortionDomain H (P.map Y) ∧ A Y = distortionFunctional H (P.map Y)) := by sorry

end RiskFunctionals.Distortion
