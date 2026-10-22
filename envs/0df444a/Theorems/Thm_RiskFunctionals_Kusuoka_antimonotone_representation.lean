-- Prove2me | Theorems.Thm_RiskFunctionals_Kusuoka_antimonotone_representation
-- name    : RiskFunctionals.Kusuoka.antimonotone_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:48.658285+00:00
-- url     : https://prove2.me/theorems/8fc2052e-5f6f-4f89-b59c-f2d7c3af9dc0
-- title:
--   Eq. (2.38) — under (C1), $\mathcal A(Y)=\inf_G\int_0^1F^{-1}(u)G^{-1}(1-u)\,du$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a non-atomic probability space, $1\le p<\infty$, and $q$ the conjugate exponent ($1/p+1/q=1$). Let $\mathcal A:L_p\to\mathbb R$ be a version-independent acceptability functional (A1)–(A3) with the dual representation
--   $$\mathcal A(Y)=\inf\{\mathbb E(YZ)-\bar A(Z): Z\in\mathcal Z_{\mathcal A}\},\qquad \mathcal Z_{\mathcal A}\subseteq L_q,$$
--   such that $(\bar A,\mathcal Z_{\mathcal A})$ is version-independent. Assume (C1): $\bar A(Z)=0$ for all $Z\in\mathcal Z_{\mathcal A}$. Then for every $Y\in L_p$ with distribution function $F$,
--   $$\mathcal A(Y)=\inf\Big\{\int_0^1F^{-1}(u)\,G^{-1}(1-u)\,du : G\in\mathcal G\Big\}, \tag{2.38}$$
--   where $\mathcal G$ is the set of distribution functions $G$ of the $Z\in\mathcal Z_{\mathcal A}$ and $F^{-1},G^{-1}$ are the quantile functions (1.3).
--
--   This is the intermediate identity of the proof of Theorem 2.45: the infimum over $Z$ can be taken over antimonotone couplings with $Y$, and only the laws of the $Z$ matter.
--
--   **Formalization Note** The infimum is indexed by $Z\in\mathcal Z_{\mathcal A}$ (each contributing its law $G$), which gives the same set of values as indexing by $G\in\mathcal G$; it is stated as a greatest lower bound in $\mathbb R$. The integral is over the open interval $(0,1)$, where both $F^{-1}(u)$ and $G^{-1}(1-u)$ are finite; the product is integrable because $F^{-1}\in L_p(0,1)$ and $G^{-1}\in L_q(0,1)$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 61, Eq. (2.38) (proof of Theorem 2.45)

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory ProbabilityTheory

namespace RiskFunctionals.Kusuoka

/-- Pflug & Römisch, p. 61, Eq. (2.38) (in the proof of Theorem 2.45): under the hypotheses of
Theorem 2.45 and (C1), `𝒜(Y) = inf {∫ F⁻¹(u) G⁻¹(1 − u) du : G ∈ 𝒢}`, where `F` is the
distribution of `Y` and `𝒢` the set of distributions of the `Z ∈ 𝒵_𝒜`. -/
theorem antimonotone_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P)
    {p q : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hpq : p.HolderConjugate q)
    (𝒜 : Lp ℝ p P → ℝ) (h𝒜 : IsAcceptabilityFunctional P 𝒜)
    (h𝒜vi : IsVersionIndependent P 𝒜)
    (𝒵𝒜 : Set (Lp ℝ q P)) (A : Lp ℝ q P → ℝ)
    (hrep : HasDualRepresentation P 𝒜 𝒵𝒜 A) (hAvi : IsVersionIndependentDual P 𝒵𝒜 A)
    (hC1 : ∀ Z ∈ 𝒵𝒜, A Z = 0) :
    ∀ Y : Lp ℝ p P,
      IsGLB {x : ℝ | ∃ Z ∈ 𝒵𝒜, x = ∫ u in Set.Ioo 0 1,
        quantileFunction (P.map Y) u * quantileFunction (P.map Z) (1 - u)} (𝒜 Y) := by sorry

end RiskFunctionals.Kusuoka
