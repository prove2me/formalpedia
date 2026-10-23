-- Prove2me | Theorems.Thm_RiskFunctionals_Kusuoka_kusuoka_representation_signed
-- name    : RiskFunctionals.Kusuoka.kusuoka_representation_signed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:51.045802+00:00
-- url     : https://prove2.me/theorems/407a3db5-c272-426c-9d77-cbea018a1ab5
-- title:
--   Theorem 2.45(iii) — representation under (C1) with two families of measures
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a non-atomic probability space, $1\le p<\infty$, $q$ the conjugate exponent, and $\mathcal A:L_p\to\mathbb R$ a version-independent acceptability functional (A1)–(A3) with dual representation $\mathcal A(Y)=\inf\{\mathbb E(YZ)-\bar A(Z): Z\in\mathcal Z_{\mathcal A}\}$, $\mathcal Z_{\mathcal A}\subseteq L_q$, where $(\bar A,\mathcal Z_{\mathcal A})$ is version-independent. Assume (C1) $\bar A(Z)=0$ for all $Z\in\mathcal Z_{\mathcal A}$. Then there is a family $\mathcal G$ of pairs $(m^{(1)}_G,m^{(2)}_G)$ of non-negative measures, $m^{(1)}_G$ on $(0,1]$ and $m^{(2)}_G$ on $(0,1)$, such that for every $Y\in L_p$
--   $$\mathcal A(Y)=\inf\Big\{\int_{(0,1]}\mathbb{AV@R}_\alpha(Y)\,dm^{(1)}_G(\alpha)-\int_{(0,1)}\mathbb{AV@R}_{1-\alpha}(-Y)\,dm^{(2)}_G(\alpha) : G\in\mathcal G\Big\}.$$
--
--   This is the form the representation takes when the dual variables are allowed to change sign; the sign in front of the second integral is the one printed in the statement.
--
--   **Formalization Note** The book places $m^{(2)}_G$ on $(0,1]$; at $\alpha=1$ the integrand would be $\mathbb{AV@R}_0(-Y)$, outside the domain $0<\alpha\le1$ of Definition 2.33 (and possibly $-\infty$ for $Y\in L_p$), so $m^{(2)}_G$ is required to put no mass at $1$. For every $Y$ and every pair, both integrands are required to be integrable, so each integral is a finite number; the infimum is a greatest lower bound in $\mathbb R$ and the family is chosen before $Y$. The printed proof derives the formula with $+$ in front of the second integral (FINDINGS F3); the statement keeps the printed $-$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 60, Theorem 2.45(iii)

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory ProbabilityTheory

namespace RiskFunctionals.Kusuoka

/-- Pflug & Römisch, p. 60, Theorem 2.45(iii), as printed: under (C1),
`𝒜(Y) = inf {∫ 𝔸𝕍@ℝ_α(Y) dm⁽¹⁾(α) − ∫ 𝔸𝕍@ℝ_{1−α}(−Y) dm⁽²⁾(α)}` over a family of pairs of
non-negative measures. The second measure of each pair sits on `(0, 1)`, where `1 − α` lies in
the domain `(0, 1]` of `𝔸𝕍@ℝ`. -/
theorem kusuoka_representation_signed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P)
    {p q : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hpq : p.HolderConjugate q)
    (𝒜 : Lp ℝ p P → ℝ) (h𝒜 : IsAcceptabilityFunctional P 𝒜)
    (h𝒜vi : IsVersionIndependent P 𝒜)
    (𝒵𝒜 : Set (Lp ℝ q P)) (A : Lp ℝ q P → ℝ)
    (hrep : HasDualRepresentation P 𝒜 𝒵𝒜 A) (hAvi : IsVersionIndependentDual P 𝒵𝒜 A)
    (hC1 : ∀ Z ∈ 𝒵𝒜, A Z = 0) :
    ∃ 𝒢 : Set (Measure ℝ × Measure ℝ),
      (∀ m ∈ 𝒢, m.1 (Set.Ioc 0 1)ᶜ = 0 ∧ m.2 (Set.Ioo 0 1)ᶜ = 0) ∧
      ∀ Y : Lp ℝ p P,
        (∀ m ∈ 𝒢,
          Integrable (fun α => averageValueAtRisk P Y α) (m.1.restrict (Set.Ioc 0 1)) ∧
          Integrable (fun α => averageValueAtRisk P (fun ω => -Y ω) (1 - α))
            (m.2.restrict (Set.Ioo 0 1))) ∧
        IsGLB {x : ℝ | ∃ m ∈ 𝒢, x =
          (∫ α in Set.Ioc 0 1, averageValueAtRisk P Y α ∂m.1) -
            ∫ α in Set.Ioo 0 1, averageValueAtRisk P (fun ω => -Y ω) (1 - α) ∂m.2} (𝒜 Y) := by sorry

end RiskFunctionals.Kusuoka
