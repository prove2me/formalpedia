-- Prove2me | Theorems.Thm_RiskFunctionals_Conditional_condAVaR_properties
-- name    : RiskFunctionals.Conditional.condAVaR_properties
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:41.672115+00:00
-- url     : https://prove2.me/theorems/3d0f6e5a-38e8-4f05-be6b-dc5a248925e1
-- title:
--   Proposition 2.57 — properties of the conditional $\mathbb{AV@R}$ (as printed)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal F_1\subseteq\mathcal F$ a sub-$\sigma$-field and $0<\alpha\le1$. Write $\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)$ for any class in $L_1(\mathcal F_1)$ satisfying, for all $B\in\mathcal F_1$,
--   $$\mathbb E[\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)\mathbb 1_B]=\inf\Big\{\mathbb E(YZ):\mathbb E(Z\mid\mathcal F_1)=\mathbb 1_B,\ 0\le Z\le\tfrac1\alpha\mathbb 1_B\Big\}.\tag{2.57}$$
--   All relations below hold almost surely.
--
--   1. (i) It is version-independent in the sense of Definition 2.55: there is a function $\Phi$ on distribution functions such that, for every $Y\in L_1(\mathcal F)$ and every version $G(\cdot\mid\mathcal F_1)$ of the conditional distribution function of $Y$, $\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)(\omega)=\Phi(G(\cdot\mid\mathcal F_1)(\omega))$ almost surely. And for every $Y\in L_1(\mathcal F)$ there is exactly one such class: the conditional $\mathbb{AV@R}_\alpha$ maps $L_1(\mathcal F)$ to $L_1(\mathcal F_1)$.
--   2. (ii) For $\mathcal F_1$-measurable $\Lambda$ with $0\le\Lambda\le1$: $\mathbb{AV@R}_\alpha(\Lambda Y^{(1)}+(1-\Lambda)Y^{(2)}\mid\mathcal F_1)\ge\Lambda\,\mathbb{AV@R}_\alpha(Y^{(1)}\mid\mathcal F_1)+(1-\Lambda)\mathbb{AV@R}_\alpha(Y^{(2)}\mid\mathcal F_1)$.
--   3. (iii) For non-negative, bounded, $\mathcal F_1$-measurable $\Lambda$: $\mathbb{AV@R}_\alpha(\Lambda Y\mid\mathcal F_1)=\Lambda\,\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)$.
--   4. (iv) If $Y^{(1)}\le Y^{(2)}$ then $\mathbb{AV@R}_\alpha(Y^{(1)}\mid\mathcal F_1)\le\mathbb{AV@R}_\alpha(Y^{(2)}\mid\mathcal F_1)$.
--   5. (v) If $Y$ is $\mathcal F_1$-measurable then $\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)=Y$.
--   6. (vi) For the trivial $\sigma$-field $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathbb{AV@R}_\alpha(Y\mid\mathcal F_0)=\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G_Y^{-1}(u)\,du$.
--   7. (vii) If $0<\alpha_1\le\alpha_2\le1$ then $\mathbb{AV@R}_{\alpha_1}(Y\mid\mathcal F_1)\le\mathbb{AV@R}_{\alpha_2}(Y\mid\mathcal F_1)$.
--   8. (viii) $\mathbb{AV@R}_1(Y\mid\mathcal F_1)=\mathbb E(Y\mid\mathcal F_1)$.
--   9. (ix) If $\mathcal F_1\subseteq\mathcal F_2\subseteq\mathcal F$, then
--   $$\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)\le\mathbb E[\mathbb{AV@R}_\alpha(Y\mid\mathcal F_2)\mid\mathcal F_1]\le\mathbb{AV@R}_\alpha(\mathbb E(Y\mid\mathcal F_2)\mid\mathcal F_1).\tag{2.58}$$
--
--   These properties make the conditional average value-at-risk the model conditional acceptability mapping used for multi-period risk in later chapters.
--
--   **Formalization Note** The conditional $\mathbb{AV@R}$ is the predicate `IsConditionalAVaR` on classes in `lpMeas ℝ ℝ m 1 P`; clauses (ii)–(ix) hold for every class satisfying it, and products such as $\Lambda Y$ and $\mathbb E(Y\mid\mathcal F_2)$ enter through an element $W$ of `Lp ℝ 1 P` a.e. equal to them. "$Y\lhd\mathcal F_1$" in (v) is $Y\in$ `lpMeas ℝ ℝ m 1 P`. $\mathcal F_0$ in (vi) is the bottom $\sigma$-algebra `⊥` (the book writes $(\Omega,\emptyset)$); $\mathbb{AV@R}_\alpha(Y)$ is the lower-tail average of the left-continuous quantile of the law of $Y$. Bounded in (iii) means $\Lambda\le C$ a.s. for some $C$. Version-independence in (i) is Definition 2.55 read pointwise, as Proposition 2.56's proof uses it: one function $\Phi$ (chosen for the given $\mathbb P$, $\mathcal F_1$ and $\alpha$, the same for every $Y$) of the conditional distribution function $G(\cdot\mid\mathcal F_1)(\omega)$, defined on all real functions but only ever evaluated at distribution functions; $G$ is any version of (2.56) (predicate `IsConditionalDistributionFunction`). Statement as printed; the second inequality of (ix) is false (finding F3).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 75–76, Proposition 2.57; p. 74, Eq. (2.57)

import Mathlib
import Definitions.Def_RiskFunctionals_Conditional_ConditionalAVaR

namespace RiskFunctionals.Conditional

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007,
pp. 75–76, Proposition 2.57 (properties of the conditional `𝔸𝕍@ℝ`), for `0 < α ≤ 1` and
`ℱ₁ ⊆ ℱ`, all relations almost surely. The conditional `𝔸𝕍@ℝ` is the predicate (2.57)
(`IsConditionalAVaR`): each clause is stated for every class satisfying it. Clause (i) is
version-independence in the sense of Definition 2.55 (the class is, almost surely, a fixed
function `Φ` of the conditional distribution function `G(·|ℱ₁)`, (2.56)) and unique existence
in `L₁(ℱ₁)` ("maps `L₁(ℱ)` to `L₁(ℱ₁)`"). -/
theorem condAVaR_properties {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P] (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    -- (i) version-independence (Definition 2.55): it is a function `Φ` of the conditional
    -- distribution function `G(·|ℱ₁)` of `Y` (a.s.), one `Φ` for every `Y`
    (∃ Φ : (ℝ → ℝ) → ℝ, ∀ (Y : Lp ℝ 1 P) (V : lpMeas ℝ ℝ m 1 P) (G : Ω → ℝ → ℝ),
      IsConditionalAVaR m P α Y V → IsConditionalDistributionFunction m P (Y : Ω → ℝ) G →
        ∀ᵐ ω ∂P, (V : Lp ℝ 1 P) ω = Φ (G ω)) ∧
    -- (i) it maps `L₁(ℱ)` to `L₁(ℱ₁)`: (2.57) has exactly one solution in `L₁(ℱ₁)`
    (∀ Y : Lp ℝ 1 P, ∃! V : lpMeas ℝ ℝ m 1 P, IsConditionalAVaR m P α Y V) ∧
    -- (ii) concavity with `ℱ₁`-measurable weights `0 ≤ Λ ≤ 1`
    (∀ Λ : Ω → ℝ, Measurable[m] Λ → (∀ᵐ ω ∂P, 0 ≤ Λ ω ∧ Λ ω ≤ 1) →
      ∀ (Y₁ Y₂ W : Lp ℝ 1 P), (W : Ω → ℝ) =ᵐ[P] (fun ω => Λ ω * Y₁ ω + (1 - Λ ω) * Y₂ ω) →
      ∀ (V₁ V₂ V : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P α Y₁ V₁ →
        IsConditionalAVaR m P α Y₂ V₂ → IsConditionalAVaR m P α W V →
        ∀ᵐ ω ∂P, Λ ω * (V₁ : Lp ℝ 1 P) ω + (1 - Λ ω) * (V₂ : Lp ℝ 1 P) ω
          ≤ (V : Lp ℝ 1 P) ω) ∧
    -- (iii) homogeneity for non-negative bounded `ℱ₁`-measurable `Λ`
    (∀ Λ : Ω → ℝ, Measurable[m] Λ → (∀ᵐ ω ∂P, 0 ≤ Λ ω) → (∃ C : ℝ, ∀ᵐ ω ∂P, Λ ω ≤ C) →
      ∀ (Y W : Lp ℝ 1 P), (W : Ω → ℝ) =ᵐ[P] (fun ω => Λ ω * Y ω) →
      ∀ (V V' : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P α Y V → IsConditionalAVaR m P α W V' →
        ∀ᵐ ω ∂P, (V' : Lp ℝ 1 P) ω = Λ ω * (V : Lp ℝ 1 P) ω) ∧
    -- (iv) monotonicity
    (∀ (Y₁ Y₂ : Lp ℝ 1 P), (∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) →
      ∀ (V₁ V₂ : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P α Y₁ V₁ →
        IsConditionalAVaR m P α Y₂ V₂ → ∀ᵐ ω ∂P, (V₁ : Lp ℝ 1 P) ω ≤ (V₂ : Lp ℝ 1 P) ω) ∧
    -- (v) `Y ◁ ℱ₁` (`Y` has an `ℱ₁`-measurable version) implies `𝔸𝕍@ℝ_α(Y|ℱ₁) = Y`
    (∀ Y : Lp ℝ 1 P, Y ∈ lpMeas ℝ ℝ m 1 P →
      ∀ V : lpMeas ℝ ℝ m 1 P, IsConditionalAVaR m P α Y V →
        ((V : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P] (Y : Ω → ℝ)) ∧
    -- (vi) for the trivial σ-field `ℱ₀ = {∅, Ω}` (`⊥`), `𝔸𝕍@ℝ_α(Y|ℱ₀) = 𝔸𝕍@ℝ_α(Y)`
    (∀ (Y : Lp ℝ 1 P) (V : lpMeas ℝ ℝ (⊥ : MeasurableSpace Ω) 1 P),
      IsConditionalAVaR ⊥ P α Y V →
        ∀ᵐ ω ∂P, (V : Lp ℝ 1 P) ω = averageValueAtRisk P (Y : Ω → ℝ) α) ∧
    -- (vii) monotonicity in the level: `α₁ ≤ α₂` implies `𝔸𝕍@ℝ_{α₁}(Y|ℱ₁) ≤ 𝔸𝕍@ℝ_{α₂}(Y|ℱ₁)`
    (∀ (α₁ α₂ : ℝ), 0 < α₁ → α₁ ≤ α₂ → α₂ ≤ 1 →
      ∀ (Y : Lp ℝ 1 P) (V₁ V₂ : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P α₁ Y V₁ →
        IsConditionalAVaR m P α₂ Y V₂ → ∀ᵐ ω ∂P, (V₁ : Lp ℝ 1 P) ω ≤ (V₂ : Lp ℝ 1 P) ω) ∧
    -- (viii) `𝔸𝕍@ℝ₁(Y|ℱ₁) = 𝔼(Y|ℱ₁)`
    (∀ (Y : Lp ℝ 1 P) (V : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P 1 Y V →
      ((V : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P] P[(Y : Ω → ℝ)|m]) ∧
    -- (ix) (2.58) for `ℱ₁ ⊆ ℱ₂ ⊆ ℱ`: `𝔸𝕍@ℝ_α(Y|ℱ₁) ≤ 𝔼[𝔸𝕍@ℝ_α(Y|ℱ₂)|ℱ₁] ≤ 𝔸𝕍@ℝ_α(𝔼(Y|ℱ₂)|ℱ₁)`
    (∀ (Y : Lp ℝ 1 P) (V₁ V₃ : lpMeas ℝ ℝ m 1 P) (m₂ : MeasurableSpace Ω), m ≤ m₂ → m₂ ≤ mΩ →
      ∀ (W : Lp ℝ 1 P), (W : Ω → ℝ) =ᵐ[P] P[(Y : Ω → ℝ)|m₂] →
      ∀ V₂ : @lpMeas Ω ℝ ℝ _ _ _ m₂ mΩ 1 P,
        IsConditionalAVaR m P α Y V₁ → IsConditionalAVaR m₂ P α Y V₂ →
        IsConditionalAVaR m P α W V₃ →
        (∀ᵐ ω ∂P, (V₁ : Lp ℝ 1 P) ω ≤ P[((V₂ : Lp ℝ 1 P) : Ω → ℝ)|m] ω) ∧
          (∀ᵐ ω ∂P, P[((V₂ : Lp ℝ 1 P) : Ω → ℝ)|m] ω ≤ (V₃ : Lp ℝ 1 P) ω)) := by sorry

end RiskFunctionals.Conditional
