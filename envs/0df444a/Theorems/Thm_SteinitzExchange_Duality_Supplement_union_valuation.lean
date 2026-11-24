-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_union_valuation
-- name    : SteinitzExchange.Duality.Supplement.union_valuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:32:03.537281+00:00
-- url     : https://prove2.me/theorems/00df63bd-5739-45f3-8f73-3d247d2911f3
-- title:
--   Theorem 7.4 — the union of two valuated matroids is a valuated matroid
-- statement:
--   Let $\mathbf M_1=(E,\mathcal B_1)$ and $\mathbf M_2=(E,\mathcal B_2)$ be matroids on a finite set $E$ with valuations $\omega_1:\mathcal B_1\to\mathbb R$ and $\omega_2:\mathcal B_2\to\mathbb R$. Let $\mathcal B_1\vee\mathcal B_2$ be the family of inclusion-maximal elements of $\{X_1\cup X_2\mid X_1\in\mathcal B_1,X_2\in\mathcal B_2\}$, the base family of the union $\mathbf M_1\vee\mathbf M_2$, and
--   $$(\omega_1\vee\omega_2)(X)=\max\{\omega_1(X_1)+\omega_2(X_2)\mid X_1\cup X_2=X,\ X_1\in\mathcal B_1,\ X_2\in\mathcal B_2\}\qquad(X\in\mathcal B_1\vee\mathcal B_2).$$
--   Then $\omega_1\vee\omega_2$ is a valuation of the union $\mathbf M_1\vee\mathbf M_2$; that is, $\mathcal B_1\vee\mathcal B_2$ is a matroid base family and $\omega_1\vee\omega_2$ satisfies (MV) on it.
--
--   The theorem extends the matroid union theorem to valuated matroids.
--
--   **Formalization Note.** `IsValuatedMatroid` is "matroid base family and (MV)"; the maximum defining $\omega_1\vee\omega_2$ ranges over all pairs with union $X$, not only disjoint ones.
--
--   Differences from the source: none.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 306, Theorem 7.4

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_Supplement_ValuatedMatroid
import Definitions.Def_SteinitzExchange_Duality_Supplement_MatroidUnion

namespace SteinitzExchange.Duality.Supplement

/-- Murota 1996, p. 306, Theorem 7.4. Let `M₁ = (E, ℬ₁)` and `M₂ = (E, ℬ₂)` be matroids with
valuations `ω₁, ω₂`. Then `ω₁ ∨ ω₂`,
`(ω₁ ∨ ω₂)(X) = max{ω₁(X₁) + ω₂(X₂) | X₁ ∪ X₂ = X, X₁ ∈ ℬ₁, X₂ ∈ ℬ₂}`, is a valuation of the
union `M₁ ∨ M₂ = (E, ℬ₁ ∨ ℬ₂)`, where `ℬ₁ ∨ ℬ₂` is the family of maximal sets `X₁ ∪ X₂`. -/
theorem union_valuation {E : Type*} [Fintype E] [DecidableEq E]
    (ℬ₁ ℬ₂ : Finset (Finset E)) (ω₁ ω₂ : Finset E → ℝ)
    (h₁ : IsValuatedMatroid ℬ₁ ω₁) (h₂ : IsValuatedMatroid ℬ₂ ω₂) :
    IsValuatedMatroid (unionBases ℬ₁ ℬ₂) (unionValue ℬ₁ ω₁ ℬ₂ ω₂) := by sorry

end SteinitzExchange.Duality.Supplement
