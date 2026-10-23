-- Prove2me | Theorems.Thm_RiskFunctionals_NestedAVaR_composition_properties
-- name    : RiskFunctionals.NestedAVaR.composition_properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:18.583495+00:00
-- url     : https://prove2.me/theorems/770d8aeb-b167-4c57-b429-ad598d38c985
-- title:
--   Proposition 3.33 — compositions of conditional acceptability mappings
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $\mathcal F_0=\{\emptyset,\Omega\}\subseteq\mathcal F_1\subseteq\dots\subseteq\mathcal F_T=\mathcal F$, let $p\in[1,\infty)$, $\mathcal Y_t=L_p(\mathcal F_t)$, $\mathcal Y=\mathcal Y_1\times\dots\times\mathcal Y_T$, and let $\mathcal A_{t-1}:\mathcal Y_T\to\mathcal Y_{t-1}$, $t=1,\dots,T$, be conditional acceptability mappings, i.e. satisfying (CA1)–(CA3). Let $\mathcal A(\cdot;\boldsymbol{\mathcal F})$ be the nested functional (3.45) and $\mathcal A^{(t)}=\mathcal A_0\circ\dots\circ\mathcal A_{t-1}$ the compositions (3.46). Then:
--
--   1. (MA1′) $\mathcal A(Y_1,\dots,Y_t+c,\dots,Y_T;\boldsymbol{\mathcal F})=c+\mathcal A(Y;\boldsymbol{\mathcal F})$ for every $Y\in\mathcal Y$, $t\in\{1,\dots,T\}$ and constant $c$;
--   2. (MA2) $Y\mapsto\mathcal A(Y;\boldsymbol{\mathcal F})$ is concave on $\mathcal Y$;
--   3. (MA3) $Y_t\le\tilde Y_t$ a.s. for all $t$ implies $\mathcal A(Y;\boldsymbol{\mathcal F})\le\mathcal A(\tilde Y;\boldsymbol{\mathcal F})$;
--   4. every $\mathcal A^{(t)}:\mathcal Y_T\to\mathbb R$, $t=1,\dots,T$, is an acceptability functional: translation-equivariant $\mathcal A^{(t)}(Y_T+c)=\mathcal A^{(t)}(Y_T)+c$, concave and monotone;
--   5. the cumulative formula holds:
--   $$\mathcal A(Y;\boldsymbol{\mathcal F})=\mathcal A^{(T)}(Y_1+\dots+Y_T);\tag{3.47}$$
--   6. if every $\mathcal A_t$ is positively homogeneous, then $\mathcal A(\lambda Y;\boldsymbol{\mathcal F})=\lambda\mathcal A(Y;\boldsymbol{\mathcal F})$ and $\mathcal A^{(t)}(\lambda Y_T)=\lambda\mathcal A^{(t)}(Y_T)$ for all $\lambda>0$.
--
--   The proposition shows that predictable translation-equivariance turns the nested definition into a cumulative one, so the nested functional depends on the process only through its total $Y_1+\dots+Y_T$; the nested average value-at-risk is the instance where every $\mathcal A_t$ is a conditional average value-at-risk.
--
--   **Formalization Note** The values of $\mathcal A(Y;\boldsymbol{\mathcal F})$ and $\mathcal A^{(t)}(Y_T)$ are the expectations of the $\mathcal F_0$-measurable random variables the recursion produces (`nestedValue`, `compositionValue`); with $\mathcal F_0$ trivial these are their constant values. Membership in $\mathcal Y$ is required only for the components $Y_1,\dots,Y_T$ of `Y : ℕ → Ω → ℝ`. The shift in (MA1′) is `Function.update Y t (Y t + c)`.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 155, Proposition 3.33 (setting: p. 154, §3.3.4; (MA1′)–(MA3): pp. 133–134, Definition 3.14; (A1)–(A3): pp. 35–36, Definition 2.17)

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions

namespace RiskFunctionals.NestedAVaR

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 155,
Proposition 3.33. Setting of §3.3.4 (p. 154): `(Ω, ℱ, P)` a probability space, a filtration
`ℱ₀ = {∅, Ω} ⊆ ℱ₁ ⊆ ⋯ ⊆ ℱ_T = ℱ`, `𝒴_t = L_p(ℱ_t)` for some `p ∈ [1, ∞)`,
`𝒴 = 𝒴₁ × ⋯ × 𝒴_T`, and conditional acceptability mappings `𝒜_{t−1} : 𝒴_T → 𝒴_{t−1}`
satisfying (CA1)–(CA3). Then the nested functional `𝒜(·; 𝓕)` of (3.45) satisfies
(MA1′) weak translation-equivariance, (MA2) concavity and (MA3) monotonicity; every
`𝒜⁽ᵗ⁾ = 𝒜₀ ∘ ⋯ ∘ 𝒜_{t−1}` of (3.46), `t = 1, …, T`, satisfies (A1)–(A3) on `𝒴_T`;
`𝒜(Y; 𝓕) = 𝒜⁽ᵀ⁾(Y₁ + ⋯ + Y_T)` (3.47); and if every `𝒜_t` is positively homogeneous, so are
`𝒜` and every `𝒜⁽ᵗ⁾`. Values are the real numbers `𝔼[·]` of the `ℱ₀`-measurable outputs. -/
theorem composition_properties {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (p : ENNReal) (hp₁ : 1 ≤ p) (hp_top : p ≠ ⊤)
    (A : ℕ → (Ω → ℝ) → Ω → ℝ) (hA : IsConditionalAcceptabilityFamily ℱ P p T A) :
    -- (MA1′) weak translation-equivariance (3.16)
    (∀ Y : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      ∀ t ∈ Finset.Icc 1 T, ∀ c : ℝ,
        nestedValue P A (Function.update Y t (fun ω => Y t ω + c)) T
          = c + nestedValue P A Y T) ∧
    -- (MA2) concavity
    (∀ Y Y' : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y' t)) →
      ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
        l * nestedValue P A Y T + (1 - l) * nestedValue P A Y' T
          ≤ nestedValue P A (l • Y + (1 - l) • Y') T) ∧
    -- (MA3) monotonicity
    (∀ Y Y' : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y' t)) →
      (∀ t ∈ Finset.Icc 1 T, Y t ≤ᵐ[P] Y' t) →
        nestedValue P A Y T ≤ nestedValue P A Y' T) ∧
    -- every 𝒜⁽ᵗ⁾ is a (single-period) acceptability functional on 𝒴_T: (A1)–(A3)
    (∀ t ∈ Finset.Icc 1 T,
      (∀ X : Ω → ℝ, IsLp (ℱ T) P p X → ∀ c : ℝ,
        compositionValue P A t (fun ω => X ω + c) = compositionValue P A t X + c) ∧
      (∀ X X' : Ω → ℝ, IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' →
        ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
          l * compositionValue P A t X + (1 - l) * compositionValue P A t X'
            ≤ compositionValue P A t (l • X + (1 - l) • X')) ∧
      (∀ X X' : Ω → ℝ, IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' → X ≤ᵐ[P] X' →
        compositionValue P A t X ≤ compositionValue P A t X')) ∧
    -- (3.47)
    (∀ Y : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      nestedValue P A Y T
        = compositionValue P A T (fun ω => ∑ t ∈ Finset.Icc 1 T, Y t ω)) ∧
    -- positive homogeneity is inherited from the 𝒜_t
    (IsPositivelyHomogeneousFamily ℱ P p T A →
      (∀ Y : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
        ∀ l : ℝ, 0 < l → nestedValue P A (l • Y) T = l * nestedValue P A Y T) ∧
      (∀ t ∈ Finset.Icc 1 T, ∀ X : Ω → ℝ, IsLp (ℱ T) P p X →
        ∀ l : ℝ, 0 < l → compositionValue P A t (l • X) = l * compositionValue P A t X)) := by sorry

end RiskFunctionals.NestedAVaR
