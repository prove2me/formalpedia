-- Prove2me | Theorems.Thm_RiskFunctionals_MultiPeriod_weak_representation
-- name    : RiskFunctionals.MultiPeriod.weak_representation
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:05.560278+00:00
-- url     : https://prove2.me/theorems/6b970bab-e8f4-401b-85f0-50ad2888aadd
-- title:
--   Theorem 3.21 — dual representation under weak translation-equivariance (MA1′)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\boldsymbol{\mathcal F}=(\mathcal F_t)_{t=0}^T$ a filtration with $\mathcal F_0=\{\emptyset,\Omega\}$, $p\in[1,\infty)$ and $1/p+1/q=1$. Let $\mathcal Y=\times_{t=1}^TL_p(\mathcal F_t)$ and $\mathcal Z=\times_{t=1}^TL_q(\mathcal F_t)$, and let $\mathcal A^+$ denote the conjugate (3.19).
--
--   1. Let $\mathcal A=\mathcal A(\cdot\,;\boldsymbol{\mathcal F})$ be an upper semicontinuous multi-period probability functional satisfying (MA1′), (MA2) and (MA3). Then, for every $Y\in\mathcal Y$,
--   $$\mathcal A(Y)=\inf_{Z\in\mathcal Z}\Big\{\sum_{t=1}^T\mathbb E(Y_tZ_t)-\mathcal A^+(Z)\ \Big|\ Z_t\ge0,\ \mathbb E(Z_t)=1,\ t=1,\dots,T\Big\}.\tag{3.22}$$
--   2. Conversely, suppose that $\mathcal A$ can be represented in the form (3.21), that is, as the infimum of $\sum_t\mathbb E(Y_tZ_t)-\mathcal A^+(Z)$ over $Z_t\ge0$, $\mathbb E(Z_t\mid\mathcal F_{t-1})=1$, for some proper functional $\mathcal A^+:\mathcal Z\to\overline{\mathbb R}$. Then $\mathcal A$ is proper, upper semicontinuous and satisfies (MA1′), (MA2) and (MA3).
--
--   The theorem replaces predictable translation-equivariance by its weak form and correspondingly relaxes the martingale-type constraint of (3.21) to a constraint on the means of the $Z_t$.
--
--   **Formalization Note** A multi-period probability functional is an `EReal`-valued functional that does not take both values $+\infty$ and $-\infty$ (the book's convention, p. 27); this is a hypothesis of part 1. The converse is stated with (3.21), as printed; (3.22) is evidently meant. "Proper" for $\mathcal A^+$ and $\mathcal A$ means $<+\infty$ everywhere and $>-\infty$ somewhere. Infima are in `EReal`, and upper semicontinuity is in the product topology. A process is indexed by $t\in\{0,\dots,T-1\}$ in Lean, shifted by one from the book.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 138, Theorem 3.21

import Mathlib
import Definitions.Def_RiskFunctionals_MultiPeriod_Functionals

namespace RiskFunctionals.MultiPeriod

open MeasureTheory

/-- Theorem 3.21 (Pflug & Römisch, p. 138), on `𝒴 = ×_{t=1}^T L_p(ℱ_t)`,
`𝒵 = ×_{t=1}^T L_q(ℱ_t)`, `1 ≤ p < ∞`, `1/p + 1/q = 1`, for a filtration with trivial `ℱ₀`.
(1) If `𝒜` is an upper semicontinuous multi-period probability functional (extended real valued,
not taking both `+∞` and `−∞`, p. 27) satisfying (MA1′), (MA2) and (MA3), then for every `Y`
`𝒜(Y) = inf{Σ_t 𝔼(Y_t Z_t) − 𝒜⁺(Z) : Z_t ≥ 0, 𝔼(Z_t) = 1, t = 1, …, T}` (3.22).
(2) Conversely, if `𝒜` can be represented in the form (3.21) (as printed) for some proper
`𝒜⁺ : 𝒵 → ℝ̄`, then `𝒜` is proper, upper semicontinuous and satisfies (MA1′), (MA2), (MA3). -/
theorem weak_representation {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] (𝔽 : Filtration (Fin (T + 1)) m0) (h𝔽 : 𝔽 0 = ⊥) :
    (∀ A : ProcessSpace P T p 𝔽 → EReal, IsProbabilityFunctional A →
      UpperSemicontinuous A → IsWeakTranslationEquivariant P 𝔽 A → IsConcaveFunctional A →
      IsMonotoneFunctional P 𝔽 A →
      ∀ Y : ProcessSpace P T p 𝔽,
        A Y = ⨅ Z ∈ densities P T q 𝔽, ((pairing Z Y : ℝ) : EReal) - concaveConj q A Z) ∧
    (∀ (A : ProcessSpace P T p 𝔽 → EReal) (Aplus : ProcessSpace P T q 𝔽 → EReal),
      IsProper Aplus →
      (∀ Y : ProcessSpace P T p 𝔽,
        A Y = ⨅ Z ∈ predictableDensities P T q 𝔽, ((pairing Z Y : ℝ) : EReal) - Aplus Z) →
      IsProper A ∧ UpperSemicontinuous A ∧ IsWeakTranslationEquivariant P 𝔽 A ∧
        IsConcaveFunctional A ∧ IsMonotoneFunctional P 𝔽 A) := by sorry

end RiskFunctionals.MultiPeriod
