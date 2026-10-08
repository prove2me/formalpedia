-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_G_concave
-- name    : SSDConstraint.Optimality.G_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:09:02.885491+00:00
-- url     : https://prove2.me/theorems/d0339544-cbb7-4e3b-9945-6ca273affc22
-- title:
--   Proof of Theorem 4.2 (p. 8) — the operator $G(X)=F_2(Y;\cdot)-F_2(X;\cdot)$ is $K$-concave
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $Y\in\mathcal L^1$ and $a,b\in\mathbb R$. Define, for $X\in\mathcal L^1$,
--   $$G(X)(\eta)=F_2(Y;\eta)-F_2(X;\eta),\qquad \eta\in[a,b].$$
--   Then $G$ is concave with respect to the cone $K$ of nonnegative functions on $[a,b]$: for all $X_1,X_2\in\mathcal L^1$, all $\lambda\in[0,1]$ and all $\eta\in[a,b]$,
--   $$\lambda G(X_1)(\eta)+(1-\lambda)G(X_2)(\eta)\le G(\lambda X_1+(1-\lambda)X_2)(\eta).$$
--
--   This puts the constraint $G(X)\in K$ in the form required by convex duality theory in the space $\mathcal C([a,b])$.
--
--   **Formalization Note** Membership in $K$ is stated pointwise on $[a,b]$; the continuity of $G(X)$ (so that it lies in $\mathcal C([a,b])$) is not part of the statement.
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 8, proof of Theorem 4.2, definition of G and K and the display following 'The operator G is concave with respect to the cone K'

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem
open MeasureTheory

namespace SSDConstraint.Optimality

/-- Proof of Theorem 4.2, p. 8: the operator `G(X)(η) = F₂(Y; η) − F₂(X; η)`, `η ∈ [a, b]`, is concave
with respect to the cone `K` of nonnegative functions: for all `X₁, X₂ ∈ L¹` and `λ ∈ [0, 1]`,
`G(λX₁ + (1 − λ)X₂) − [λG(X₁) + (1 − λ)G(X₂)]` is nonnegative at every `η ∈ [a, b]`. -/
theorem G_concave {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω →₁[P] ℝ) (a b : ℝ) :
    ∀ X₁ X₂ : Ω →₁[P] ℝ, ∀ l ∈ Set.Icc (0 : ℝ) 1, ∀ η ∈ Set.Icc a b,
      l * (F2 P Y η - F2 P X₁ η) + (1 - l) * (F2 P Y η - F2 P X₂ η) ≤
        F2 P Y η - F2 P (l • X₁ + (1 - l) • X₂) η := by sorry

end SSDConstraint.Optimality
