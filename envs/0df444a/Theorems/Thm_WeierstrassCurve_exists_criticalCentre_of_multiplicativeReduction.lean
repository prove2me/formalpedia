-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
-- name    : WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/1459e706-bb49-57aa-833f-a51df68be7b3
-- title:
--   Inertia-fixed critical centre at a multiplicative prime
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$, with coefficients $a_1,a_2,a_3,a_4,a_6$ and the usual invariants $\Delta$, $c_4$, $b_2$, and let $q$ be a prime number. Assume $\Delta \neq 0$, $q \mid \Delta$ and $q \nmid c_4$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ (the Mathlib algebraic closure of $\mathbb Q$) satisfying `LiesOverPrime q`, that is, the image of $q$ in $\overline{\mathbb Q}$ is a nonunit of $A$, so $q$ lies in the maximal ideal of $A$. Then there exist $x_0, y_0 \in A$ such that, writing $F(x,y) = y^2 + a_1xy + a_3y - (x^3 + a_2x^2 + a_4x + a_6)$: the partial derivatives of $F$ vanish at $(x_0,y_0)$, in the form $2y_0 + a_1x_0 + a_3 = 0$ and $a_1y_0 = 3x_0^2 + 2a_2x_0 + a_4$; the element $b_2 + 12x_0$ has valuation $1$ with respect to $A$, i.e. it is a unit of $A$; the value $F(x_0,y_0)$ has valuation $< 1$, i.e. lies in the maximal ideal of $A$; and every $\sigma$ in `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup, fixes both $x_0$ and $y_0$.
--
--   At a prime $q$ of multiplicative reduction, detected here by the conditions $q \mid \Delta$ and $q \nmid c_4$, the reduction of $W$ modulo the maximal ideal of $A$ is a nodal cubic, and the statement produces an inertia-invariant critical point of the Weierstrass polynomial over $A$ lifting that node, the translation $(x,y) \mapsto (x + x_0, y + y_0)$ then putting $W$ into a normalised shape with non-degenerate tangent cone. It serves as the normalisation step for the elementary analysis of the local Galois action at a multiplicative prime, and is used by the lemmas on decomposition and inertia for a Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ x₀ y₀ : AlgebraicClosure ℚ, x₀ ∈ A ∧ y₀ ∈ A ∧
      2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0 ∧
      (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ ∧
      A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1 ∧
      A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1 ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        σ x₀ = x₀ ∧ σ y₀ = y₀) := by sorry
