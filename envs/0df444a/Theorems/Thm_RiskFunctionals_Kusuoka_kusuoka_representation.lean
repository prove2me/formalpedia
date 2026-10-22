-- Prove2me | Theorems.Thm_RiskFunctionals_Kusuoka_kusuoka_representation
-- name    : RiskFunctionals.Kusuoka.kusuoka_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:54.01597+00:00
-- url     : https://prove2.me/theorems/ed7d90da-2b59-45c3-bfbf-164ac9c1edf2
-- title:
--   Theorem 2.45(i) — Kusuoka representation of version-independent acceptability functionals
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a non-atomic probability space, $1\le p<\infty$, and $q$ the conjugate exponent ($1/p+1/q=1$), so that $L_q$ is the dual space of $L_p=L_p(\Omega,\mathcal F,\mathbb P)$. Let $\mathcal A:L_p\to\mathbb R$ be a version-independent acceptability functional, i.e. translation equivariant (A1), concave (A2), monotone (A3), and depending only on the distribution of its argument. Suppose that
--   $$\mathcal A(Y)=\inf\{\mathbb E(YZ)-\bar A(Z) : Z\in\mathcal Z_{\mathcal A}\}\qquad(Y\in L_p)$$
--   for a set $\mathcal Z_{\mathcal A}\subseteq L_q$ and a function $\bar A$ such that $(\bar A,\mathcal Z_{\mathcal A})$ is version-independent (if $Z\overset d=\tilde Z$, then both or none lie in $\mathcal Z_{\mathcal A}$, and $\bar A(Z)=\bar A(\tilde Z)$). Assume
--
--   - (C1) $\bar A(Z)=0$ for all $Z\in\mathcal Z_{\mathcal A}$;
--   - (C2) every $Z\in\mathcal Z_{\mathcal A}$ is non-negative a.s.;
--   - (C3) every $Z\in\mathcal Z_{\mathcal A}$ satisfies $\mathbb E(Z)=1$.
--
--   Then there is a family $\mathcal G$ of probability measures on $(0,1]$, not depending on $Y$, such that for every $Y\in L_p$
--   $$\mathcal A(Y)=\inf\Big\{\int_{(0,1]}\mathbb{AV@R}_\alpha(Y)\,dm(\alpha) : m\in\mathcal G\Big\}, \tag{2.37}$$
--   where $\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha F^{-1}(u)\,du$ is the lower-tail average value-at-risk of $Y$ (distribution function $F$).
--
--   This is Kusuoka's theorem in the profit convention: every such functional is the lower envelope of mixtures of average values-at-risk, so $\mathbb{AV@R}$ is the basic building block of law-invariant coherent acceptability.
--
--   **Formalization Note** Measures on $(0,1]$ are measures on $\mathbb R$ giving zero mass to the complement of $(0,1]$. The conclusion also asserts that for every $Y$ and every $m\in\mathcal G$ the map $\alpha\mapsto\mathbb{AV@R}_\alpha(Y)$ is $m$-integrable on $(0,1]$, so that each integral in (2.37) is a finite real number (in the book's extended-real reading, an integral equal to $-\infty$ would make the infimum $-\infty\neq\mathcal A(Y)$, and $\mathbb{AV@R}_\alpha(Y)\le\mathbb EY$ excludes $+\infty$). The infimum is a greatest lower bound in $\mathbb R$, so $\mathcal G$ is nonempty. The family is chosen before $Y$. The hypothesis $1\le p$ is implied by $1/p+1/q=1$ and is kept as printed.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 59–60, Theorem 2.45(i), Eq. (2.37)

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory ProbabilityTheory

namespace RiskFunctionals.Kusuoka

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, pp. 59–60,
Theorem 2.45(i), (2.37): Kusuoka representation under (C1), (C2), (C3). -/
theorem kusuoka_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P)
    {p q : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hpq : p.HolderConjugate q)
    (𝒜 : Lp ℝ p P → ℝ) (h𝒜 : IsAcceptabilityFunctional P 𝒜)
    (h𝒜vi : IsVersionIndependent P 𝒜)
    (𝒵𝒜 : Set (Lp ℝ q P)) (A : Lp ℝ q P → ℝ)
    (hrep : HasDualRepresentation P 𝒜 𝒵𝒜 A) (hAvi : IsVersionIndependentDual P 𝒵𝒜 A)
    (hC1 : ∀ Z ∈ 𝒵𝒜, A Z = 0)
    (hC2 : ∀ Z ∈ 𝒵𝒜, ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hC3 : ∀ Z ∈ 𝒵𝒜, ∫ ω, Z ω ∂P = 1) :
    ∃ 𝒢 : Set (Measure ℝ),
      (∀ m ∈ 𝒢, IsProbabilityMeasure m ∧ m (Set.Ioc 0 1)ᶜ = 0) ∧
      ∀ Y : Lp ℝ p P,
        (∀ m ∈ 𝒢, Integrable (fun α => averageValueAtRisk P Y α) (m.restrict (Set.Ioc 0 1))) ∧
        IsGLB {x : ℝ | ∃ m ∈ 𝒢, x = ∫ α in Set.Ioc 0 1, averageValueAtRisk P Y α ∂m} (𝒜 Y) := by sorry

end RiskFunctionals.Kusuoka
