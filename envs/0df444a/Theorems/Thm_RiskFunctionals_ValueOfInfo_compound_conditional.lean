-- Prove2me | Theorems.Thm_RiskFunctionals_ValueOfInfo_compound_conditional
-- name    : RiskFunctionals.ValueOfInfo.compound_conditional
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:17.1128+00:00
-- url     : https://prove2.me/theorems/afb2cb0f-bb4b-4f1e-8cbd-5d6def95ae36
-- title:
--   Proposition 2.12 — compound linear/convex/concave functionals and conditioning
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space on a standard Borel space, $\mathcal F_1\subseteq\mathcal F$ a sub-$\sigma$-algebra, $Y$ a real random variable, and $\mathcal R$ a version-independent probability functional (a real map on distributions on $\mathbb R$). Write $\mathcal R(Y)$ for $\mathcal R$ applied to the law of $Y$, and $\mathcal R(Y\mid\mathcal F_1)$ for the random variable obtained by applying $\mathcal R$ to the conditional distribution of $Y$ given $\mathcal F_1$. Suppose $\mathbb E[\mathcal R(Y\mid\mathcal F_1)]$ exists. Assume $Y\in\operatorname{dom}\mathcal R$, i.e. the law of $Y$ lies in the domain $\mathcal D$ of $\mathcal R$, and that the conditional distribution of $Y$ given $\mathcal F_1$ lies in $\mathcal D$ almost surely. Then, with the compounding properties taken on $\mathcal D$:
--
--   1. if $\mathcal R$ is compound linear, $\mathcal R(Y)=\mathbb E[\mathcal R(Y\mid\mathcal F_1)]$;
--   2. if $\mathcal R$ is compound convex, $\mathcal R(Y)\le\mathbb E[\mathcal R(Y\mid\mathcal F_1)]$;
--   3. if $\mathcal R$ is compound concave, $\mathcal R(Y)\ge\mathbb E[\mathcal R(Y\mid\mathcal F_1)]$.
--
--   $$\mathcal R(Y)\ \ (=,\ \le,\ \ge)\ \ \mathbb E\big[\mathcal R(Y\mid\mathcal F_1)\big].$$
--
--   This is the random-variable form of the compounding properties: applying the functional to the conditional distributions and averaging compares to applying it to the unconditional distribution in the direction the compounding property dictates.
--
--   **Formalization Note** The conditional distribution of $Y$ given $\mathcal F_1$ at $\omega$ is the image under $Y$ of Mathlib's regular conditional probability `condExpKernel P m ω`, which needs $\Omega$ standard Borel. The book's "$Y\in\operatorname{dom}\mathcal R$" is `hYdom`; that $\mathcal R(Y\mid\mathcal F_1)$ is defined, implicit in the book, is `hconddom` (the conditional distribution is in $\mathcal D$ almost surely); the existence of $\mathbb E[\mathcal R(Y\mid\mathcal F_1)]$, implicit in the book, is the integrability hypothesis `hint`. $Y$ is assumed measurable.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 34, Proposition 2.12

import Mathlib
import Definitions.Def_RiskFunctionals_ValueOfInfo_Compounding

namespace RiskFunctionals.ValueOfInfo

open MeasureTheory ProbabilityTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 34,
Proposition 2.12. Let `ℛ` be a version-independent functional on distributions on `ℝ` with domain
`𝒟`, `Y ∈ dom ℛ` a random variable (its law lies in `𝒟`) and `ℱ₁ = m` a sub-σ-algebra.
`ℛ(Y|ℱ₁)(ω)` is `ℛ` applied to the conditional distribution of `Y` given `ℱ₁`, i.e. to the image
under `Y` of the regular conditional probability `condExpKernel P m ω`, which lies in `𝒟` for
almost every `ω`. Then (i) compound linearity gives `ℛ(Y) = 𝔼[ℛ(Y|ℱ₁)]`, (ii) compound convexity
gives `ℛ(Y) ≤ 𝔼[ℛ(Y|ℱ₁)]`, (iii) compound concavity gives `ℛ(Y) ≥ 𝔼[ℛ(Y|ℱ₁)]`, whenever
`𝔼[ℛ(Y|ℱ₁)]` exists. -/
theorem compound_conditional {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (hm : m ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒟 : Set (Measure ℝ)) (ℛ : Measure ℝ → ℝ) (Y : Ω → ℝ) (hY : Measurable Y)
    (hYdom : P.map Y ∈ 𝒟) (hconddom : ∀ᵐ ω ∂P, (condExpKernel P m ω).map Y ∈ 𝒟)
    (hint : Integrable (fun ω => ℛ ((condExpKernel P m ω).map Y)) P) :
    (CompoundLinear 𝒟 ℛ → ℛ (P.map Y) = ∫ ω, ℛ ((condExpKernel P m ω).map Y) ∂P) ∧
    (CompoundConvex 𝒟 ℛ → ℛ (P.map Y) ≤ ∫ ω, ℛ ((condExpKernel P m ω).map Y) ∂P) ∧
    (CompoundConcave 𝒟 ℛ → ∫ ω, ℛ ((condExpKernel P m ω).map Y) ∂P ≤ ℛ (P.map Y)) := by sorry

end RiskFunctionals.ValueOfInfo
