-- Prove2me | Theorems.Thm_WeierstrassCurve_level_add_of_inZeroComponentAt
-- name    : WeierstrassCurve.level_add_of_inZeroComponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/b950afc9-eb90-53c2-b505-07da1cddd097
-- title:
--   Translation by a point of E⁰ preserves level and branch at a node
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with valuation $v$, and write $E$ for the base change of $W$ to $\overline{\mathbb{Q}}$ (through $\mathbb{Q}$) and $F_0 = y_0^2 + a_1x_0y_0 + a_3y_0 - (x_0^3 + a_2x_0^2 + a_4x_0 + a_6)$. Assume $x_0, y_0 \in A$ satisfy the two partial-derivative equations $2y_0 + a_1x_0 + a_3 = 0$ and $a_1y_0 = 3x_0^2 + 2a_2x_0 + a_4$, that $v(b_2 + 12x_0) = 1$, and that $v(F_0) < 1$. Let $P$ be a point of $E$ satisfying `InZeroComponentAt`, i.e. either $P = 0$, or $P = (x,y)$ affine with either $x \notin A$ or else $x, y \in A$ and the reduction of $(x,y)$ modulo the maximal ideal of $A$ is a nonsingular point of the reduction of $W$ over the residue field of $A$. Let $(x_2,y_2)$ be a nonsingular affine point of $E$ with $v(x_2 - x_0) < 1$. The conclusion is that there are $x_3, y_3$ with $(x_3,y_3)$ a nonsingular affine point of $E$ such that $P + (x_2,y_2) = (x_3,y_3)$, with $v(x_3 - x_0) < 1$, and moreover: if $v(F_0) < v(x_2-x_0)^2$ then $v(x_3 - x_0) = v(x_2 - x_0)$ and $v\bigl((y_3-y_0)/(x_3-x_0) - (y_2-y_0)/(x_2-x_0)\bigr) < 1$; and if $v(x_2-x_0)^2 \le v(F_0)$ then $v(x_3-x_0)^2 \le v(F_0)$.
--
--   This is the clause of the additivity of the component map at a place of multiplicative reduction which says that translating a point reducing to the node by a point of the identity component changes neither its level $v(x-x_0)$ nor, in the shallow case, the branch through which it passes (equality of slopes modulo the maximal ideal), while the antipodal case is preserved as a case. It feeds the analysis of torsion points lying outside the identity component and the associated computations in Vélu coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_level_add_of_inZeroComponentAt.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.level_add_of_inZeroComponentAt
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hP : W.InZeroComponentAt A P)
    {x₂ y₂ : AlgebraicClosure ℚ}
    (h₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂)
    (hX₂ : A.valuation (x₂ - x₀) < 1) :
    ∃ (x₃ y₃ : AlgebraicClosure ℚ)
      (h₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
      P + .some x₂ y₂ h₂ = .some x₃ y₃ h₃ ∧ A.valuation (x₃ - x₀) < 1 ∧
      (A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
          < A.valuation (x₂ - x₀) ^ 2 →
        A.valuation (x₃ - x₀) = A.valuation (x₂ - x₀) ∧
        A.valuation ((y₃ - y₀) / (x₃ - x₀) - (y₂ - y₀) / (x₂ - x₀)) < 1) ∧
      (A.valuation (x₂ - x₀) ^ 2 ≤
          A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) →
        A.valuation (x₃ - x₀) ^ 2 ≤
          A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) := by sorry
