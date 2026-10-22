-- Prove2me | Theorems.Thm_RiskFunctionals_NestedAVaR_condAVaR_pairing
-- name    : RiskFunctionals.NestedAVaR.condAVaR_pairing
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:07.3518+00:00
-- url     : https://prove2.me/theorems/a7a2bc2b-f365-493b-9208-5220b13ab19b
-- title:
--   Proof of Proposition 3.35, p. 156 (Eq. (2.59)) — the conditional AV@R paired with a nonnegative bounded weight
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal F_1\subseteq\mathcal F$ a sub-$\sigma$-field, $\alpha\in(0,1]$, $Y\in L_1(\mathcal F)$, and let $\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)$ be (a version of) the conditional average value-at-risk defined by (2.54). Then for every $Z_1\in L_\infty(\mathcal F_1)$ with $Z_1\ge0$,
--   $$\mathbb E\big(\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)\,Z_1\big)=\inf\Big\{\mathbb E(YZ_2):0\le Z_2\le\tfrac1\alpha Z_1,\ \mathbb E(Z_2\mid\mathcal F_1)=Z_1\Big\},$$
--   the infimum running over $Z_2\in L_\infty(\mathcal F)$.
--
--   The defining relation (2.54) is the case $Z_1=\mathbb 1_B$; this extension to bounded nonnegative weights is the step that lets conditional average values-at-risk be composed, and it is the induction step of the dual representation of the nested average value-at-risk.
--
--   **Formalization Note** The page states the identity "for $Z_1\in L_\infty(\mathcal F_1)$" and writes $\mathbb E(Z\mid\mathcal F_1)$; the cited (2.59) (p. 75) has the hypothesis that the weight is non-negative and bounded, and the constraint $0\le Z_2\le Z_1/\alpha$ is infeasible otherwise. The Lean statement takes $Z_1\ge0$ and reads $Z$ as $Z_2$. $Z_1\in L_\infty(\mathcal F_1)$ is: $\mathcal F_1$-measurable and almost surely bounded by a constant. The infimum is in `EReal`.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 156, proof of Proposition 3.35 (display citing Eq. (2.59), p. 75)

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_AverageValueAtRisk

namespace RiskFunctionals.NestedAVaR

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 156,
proof of Proposition 3.35 (citing (2.59), p. 75): the conditional `𝔸𝕍@ℝ_α` satisfies, for
`Z₁ ∈ L_∞(ℱ₁)`, `Z₁ ≥ 0`,
`𝔼(𝔸𝕍@ℝ_α(Y | ℱ₁) Z₁) = inf {𝔼(Y Z₂) : 0 ≤ Z₂ ≤ (1/α) Z₁, 𝔼(Z₂ | ℱ₁) = Z₁}`.
Here `ℱ₁ ⊆ ℱ` is `m`, `0 < α ≤ 1`, `Y ∈ L₁(ℱ)` and `V` is a version of `𝔸𝕍@ℝ_α(Y | ℱ₁)`. The
nonnegativity of `Z₁` is the hypothesis of (2.59) ("for all non-negative bounded,
`ℱ₁`-measurable `X`"); the page's "for `Z₁ ∈ L_∞(ℱ₁)`" omits it, and without it the constraint set
is empty. The page's `𝔼(Z | ℱ₁)` is read `𝔼(Z₂ | ℱ₁)`. -/
theorem condAVaR_pairing {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P] (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (Y V : Ω → ℝ) (hY : Integrable Y P) (hV : IsConditionalAVaR m P α Y V)
    (Z₁ : Ω → ℝ) (hZ₁m : Measurable[m] Z₁) (hZ₁b : ∃ C : ℝ, ∀ᵐ ω ∂P, |Z₁ ω| ≤ C)
    (hZ₁n : ∀ᵐ ω ∂P, 0 ≤ Z₁ ω) :
    ((∫ ω, V ω * Z₁ ω ∂P : ℝ) : EReal)
      = ⨅ (Z₂ : Ω → ℝ) (_ : Measurable Z₂ ∧
          (∀ᵐ ω ∂P, 0 ≤ Z₂ ω ∧ Z₂ ω ≤ (1 / α) * Z₁ ω) ∧ P[Z₂|m] =ᵐ[P] Z₁),
        ((∫ ω, Y ω * Z₂ ω ∂P : ℝ) : EReal) := by sorry

end RiskFunctionals.NestedAVaR
