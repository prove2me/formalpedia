-- Prove2me | Theorems.Thm_RiskFunctionals_MultiPeriod_multiperiod_representation
-- name    : RiskFunctionals.MultiPeriod.multiperiod_representation
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:12.543673+00:00
-- url     : https://prove2.me/theorems/d42dae21-30d8-4143-aa0d-adf3dee24434
-- title:
--   Theorem 3.20 — dual representation of upper semicontinuous multi-period acceptability functionals
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $p\in[1,\infty)$ and $1/p+1/q=1$. For a filtration $\boldsymbol{\mathcal F}=(\mathcal F_t)_{t=0}^T$ with $\mathcal F_0=\{\emptyset,\Omega\}$, let $\mathcal Y=\times_{t=1}^TL_p(\mathcal F_t)$ and $\mathcal Z=\times_{t=1}^TL_q(\mathcal F_t)$, and let $\mathcal A^+$ denote the conjugate (3.19) of $\mathcal A(\cdot\,;\boldsymbol{\mathcal F})$.
--
--   1. Let $\mathcal A=\mathcal A(\cdot\,;\boldsymbol{\mathcal F})$ be a multi-period acceptability functional (proper, (MA0)–(MA3)) that is upper semicontinuous. Then, for every $Y\in\mathcal Y$,
--   $$\mathcal A(Y)=\inf_{Z\in\mathcal Z}\Big\{\sum_{t=1}^T\mathbb E(Y_tZ_t)-\mathcal A^+(Z)\ \Big|\ Z_t\ge0,\ \mathbb E(Z_t\mid\mathcal F_{t-1})=1,\ t=1,\dots,T\Big\}.\tag{3.21}$$
--   2. Conversely, suppose that, for every filtration $\boldsymbol{\mathcal F}$ with trivial $\mathcal F_0$, $\mathcal A(\cdot\,;\boldsymbol{\mathcal F})$ can be represented in the form (3.21) for some proper functional $\mathcal A^+:\mathcal Z\to\overline{\mathbb R}$. Then $\mathcal A$ is proper, upper semicontinuous and satisfies (MA0)–(MA3).
--
--   The theorem identifies the dual variables of a predictably translation-equivariant multi-period acceptability functional as nonnegative processes whose conditional means given the previous σ-algebra are one, i.e. products of conditional densities. This is the multi-period counterpart of the single-period representation over probability densities.
--
--   **Formalization Note** $\mathcal A$ is a family indexed by filtrations, because (MA0) compares two filtrations. Part 1 assumes Definition 3.14 for the family and upper semicontinuity at the given $\boldsymbol{\mathcal F}$. Part 2 assumes the representation (3.21), each with its own $\mathcal A^+$, at every filtration, and concludes that every member is proper and upper semicontinuous and that the family satisfies (MA0)–(MA3). "Proper" means $<+\infty$ everywhere and $>-\infty$ somewhere. Infima are in `EReal`, and the conditional expectation is Mathlib's `condExp`, with constraints holding a.s. A process is indexed by $t\in\{0,\dots,T-1\}$ in Lean, shifted by one from the book.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 136, Theorem 3.20

import Mathlib
import Definitions.Def_RiskFunctionals_MultiPeriod_Functionals

namespace RiskFunctionals.MultiPeriod

open MeasureTheory

/-- Theorem 3.20 (Pflug & Römisch, p. 136), on `𝒴 = ×_{t=1}^T L_p(ℱ_t)`,
`𝒵 = ×_{t=1}^T L_q(ℱ_t)`, `1 ≤ p < ∞`, `1/p + 1/q = 1`, for filtrations with trivial `ℱ₀`.
(1) If `𝒜 = 𝒜(·; 𝓕)` is a multi-period acceptability functional (Definition 3.14) that is upper
semicontinuous at `𝓕`, then for every `Y ∈ 𝒴`
`𝒜(Y) = inf{Σ_t 𝔼(Y_t Z_t) − 𝒜⁺(Z) : Z_t ≥ 0, 𝔼(Z_t | ℱ_{t−1}) = 1, t = 1, …, T}` (3.21),
with `𝒜⁺` the conjugate (3.19).
(2) Conversely, if for every filtration `𝒜(·; 𝓕)` can be represented in the form (3.21) for
some proper functional `𝒜⁺ : 𝒵 → ℝ̄`, then `𝒜` is proper, upper semicontinuous and satisfies
(MA0)–(MA3). -/
theorem multiperiod_representation {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] :
    (∀ A : (𝔽 : Filtration (Fin (T + 1)) m0) → ProcessSpace P T p 𝔽 → EReal,
      IsMultiPeriodAcceptability P T p A →
      ∀ 𝔽 : Filtration (Fin (T + 1)) m0, 𝔽 0 = ⊥ → UpperSemicontinuous (A 𝔽) →
      ∀ Y : ProcessSpace P T p 𝔽,
        A 𝔽 Y = ⨅ Z ∈ predictableDensities P T q 𝔽,
          ((pairing Z Y : ℝ) : EReal) - concaveConj q (A 𝔽) Z) ∧
    (∀ A : (𝔽 : Filtration (Fin (T + 1)) m0) → ProcessSpace P T p 𝔽 → EReal,
      (∀ 𝔽 : Filtration (Fin (T + 1)) m0, 𝔽 0 = ⊥ →
        ∃ Aplus : ProcessSpace P T q 𝔽 → EReal, IsProper Aplus ∧
          ∀ Y : ProcessSpace P T p 𝔽,
            A 𝔽 Y = ⨅ Z ∈ predictableDensities P T q 𝔽, ((pairing Z Y : ℝ) : EReal) - Aplus Z) →
      (∀ 𝔽 : Filtration (Fin (T + 1)) m0, 𝔽 0 = ⊥ → UpperSemicontinuous (A 𝔽)) ∧
        IsMultiPeriodAcceptability P T p A) := by sorry

end RiskFunctionals.MultiPeriod
