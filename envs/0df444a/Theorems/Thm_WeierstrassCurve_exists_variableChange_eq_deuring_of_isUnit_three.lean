-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three
-- name    : WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/d69becb5-1487-5d64-a1f8-c9b83eabe34b
-- title:
--   Deuring normal form from a point of order 3
-- statement:
--   Let $M$ be a field, $A \subseteq M$ a valuation subring, and suppose $3$ is a unit in $A$. Let $E$ be a Weierstrass curve over $M$ which is elliptic (its discriminant is invertible) and whose $j$-invariant lies in $A$. Let $(x_0, y_0)$ be a nonsingular point of the affine model of $E$, and suppose the corresponding point $(x_0, y_0)$ of the group $E(M)$ satisfies $3 \cdot (x_0,y_0) = 0$. Finally let $c \in M$ satisfy $c^3 = 2y_0 + a_1 x_0 + a_3$. The assertion is that there exist $\alpha \in A$ and a Weierstrass variable change $\kappa$ over $M$ such that: the Weierstrass curve over $A$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (\alpha,0,1,0,0)$, i.e. $y^2 + \alpha xy + y = x^3$, has invertible discriminant $\Delta = \alpha^3 - 27$ in $A$; the unit $\kappa.u$ equals $c$ in $M$, $\kappa.r = x_0$, $\kappa.t = y_0$, and $\kappa.s = (3x_0^2 + 2a_2 x_0 + a_4 - a_1 y_0)/(2y_0 + a_1 x_0 + a_3)$; and the result of acting by $\kappa$ on $E$ is exactly the curve $y^2 + \alpha xy + y = x^3$ over $A$, viewed over $M$ along the inclusion $A \to M$.
--
--   This is the classical Deuring normal form: a three-torsion point, moved to the origin with its inflectional tangent horizontal, puts the curve in the shape $y^2 + \alpha xy + y = x^3$, and the stated integrality of $\alpha$ together with invertibility of $\alpha^3 - 27$ exhibits good reduction over $A$ whenever $j(E) \in A$ and $3 \in A^\times$. It provides the explicit local model used by [`WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero`](thm.html#WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three
    {M : Type u} [Field M] [DecidableEq M] (A : ValuationSubring M) (h3 : IsUnit (3 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {x₀ y₀ : M} (hP : E.toAffine.Nonsingular x₀ y₀) (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0)
    {c : M} (hc : c ^ 3 = 2 * y₀ + E.a₁ * x₀ + E.a₃) :
    ∃ (α : A) (κ : VariableChange M),
      IsUnit (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).Δ ∧
      (κ.u : M) = c ∧ κ.r = x₀ ∧
      κ.s = (3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃) ∧
      κ.t = y₀ ∧
      κ • E = (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).map A.subtype := by sorry
