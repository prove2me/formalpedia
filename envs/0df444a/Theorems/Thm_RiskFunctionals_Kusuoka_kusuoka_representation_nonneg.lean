-- Prove2me | Theorems.Thm_RiskFunctionals_Kusuoka_kusuoka_representation_nonneg
-- name    : RiskFunctionals.Kusuoka.kusuoka_representation_nonneg
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:49.059622+00:00
-- url     : https://prove2.me/theorems/b2d3d0fd-3814-440e-a660-c55656743557
-- title:
--   Theorem 2.45(ii) — representation with non-negative measures under (C1), (C2)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a non-atomic probability space, $1\le p<\infty$, $q$ the conjugate exponent, and $\mathcal A:L_p\to\mathbb R$ a version-independent acceptability functional (A1)–(A3) with dual representation $\mathcal A(Y)=\inf\{\mathbb E(YZ)-\bar A(Z): Z\in\mathcal Z_{\mathcal A}\}$, $\mathcal Z_{\mathcal A}\subseteq L_q$, where $(\bar A,\mathcal Z_{\mathcal A})$ is version-independent. Assume (C1) $\bar A(Z)=0$ and (C2) $Z\ge0$ a.s. for all $Z\in\mathcal Z_{\mathcal A}$. Then there is a family $\mathcal G$ of non-negative measures on $(0,1]$ such that for every $Y\in L_p$
--   $$\mathcal A(Y)=\inf\Big\{\int_{(0,1]}\mathbb{AV@R}_\alpha(Y)\,dm(\alpha) : m\in\mathcal G\Big\}.$$
--
--   Without the normalization (C3) the mixing measures need not be probabilities; in the book's construction the total mass of the measure attached to a law $G$ is the mean of $G$.
--
--   **Formalization Note** Measures on $(0,1]$ are measures on $\mathbb R$ with no mass outside $(0,1]$; no finiteness is imposed, as on the page. As in part (i), the conclusion also asserts that every $\alpha\mapsto\mathbb{AV@R}_\alpha(Y)$ is $m$-integrable over $(0,1]$ for $m\in\mathcal G$, so each integral is a finite number, and the infimum is a greatest lower bound in $\mathbb R$ (so $\mathcal G\neq\emptyset$). The family is chosen before $Y$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 60, Theorem 2.45(ii)

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory ProbabilityTheory

namespace RiskFunctionals.Kusuoka

/-- Pflug & Römisch, p. 60, Theorem 2.45(ii): under (C1) and (C2), a representation as an
infimum of mixtures of average values-at-risk with non-negative measures on `(0, 1]`. -/
theorem kusuoka_representation_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P)
    {p q : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hpq : p.HolderConjugate q)
    (𝒜 : Lp ℝ p P → ℝ) (h𝒜 : IsAcceptabilityFunctional P 𝒜)
    (h𝒜vi : IsVersionIndependent P 𝒜)
    (𝒵𝒜 : Set (Lp ℝ q P)) (A : Lp ℝ q P → ℝ)
    (hrep : HasDualRepresentation P 𝒜 𝒵𝒜 A) (hAvi : IsVersionIndependentDual P 𝒵𝒜 A)
    (hC1 : ∀ Z ∈ 𝒵𝒜, A Z = 0)
    (hC2 : ∀ Z ∈ 𝒵𝒜, ∀ᵐ ω ∂P, 0 ≤ Z ω) :
    ∃ 𝒢 : Set (Measure ℝ),
      (∀ m ∈ 𝒢, m (Set.Ioc 0 1)ᶜ = 0) ∧
      ∀ Y : Lp ℝ p P,
        (∀ m ∈ 𝒢, Integrable (fun α => averageValueAtRisk P Y α) (m.restrict (Set.Ioc 0 1))) ∧
        IsGLB {x : ℝ | ∃ m ∈ 𝒢, x = ∫ α in Set.Ioc 0 1, averageValueAtRisk P Y α ∂m} (𝒜 Y) := by sorry

end RiskFunctionals.Kusuoka
