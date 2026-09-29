-- Prove2me | Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
-- name    : WeierstrassCurve.inZeroComponentAt_sub_of_level_eq_of_branch_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/b1373cba-c1c3-580c-8c19-371a40e1cb9b
-- title:
--   Equal level and same branch: the difference lies in the zero component
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with valuation $v =$ `A.valuation`, and let $E$ denote the base change of $W$ to $\overline{\mathbb{Q}}$ along $\mathbb{Z} \to \mathbb{Q}$. Assume given $x_0, y_0 \in A$ that form a critical point of $F(x,y) = y^2 + a_1xy + a_3y - (x^3+a_2x^2+a_4x+a_6)$, i.e. $2y_0 + a_1x_0 + a_3 = 0$ and $a_1y_0 = 3x_0^2 + 2a_2x_0 + a_4$, with $v(b_2 + 12x_0) = 1$ (the quadratic part is a unit, so the reduction has a node there) and $v(F(x_0,y_0)) < 1$. Let $(x_1,y_1)$ and $(x_2,y_2)$ be nonsingular affine points of $E$ with $v(x_1-x_0) < 1$, $v(x_2-x_0) < 1$ and $v(x_1-x_0) = v(x_2-x_0)$ (equal level), shallow in the sense $v(F(x_0,y_0)) < v(x_1-x_0)^2$, and on the same branch in the sense that the slopes satisfy $v\bigl((y_1-y_0)/(x_1-x_0) - (y_2-y_0)/(x_2-x_0)\bigr) < 1$. Then the difference $P = (x_1,y_1) - (x_2,y_2)$ satisfies `W.InZeroComponentAt A`, i.e. either $P = 0$, or $P$ is an affine point $(x,y)$ with $x \notin A$, or $x,y \in A$ and the point obtained by reducing $x$ and $y$ to the residue field of $A$ is nonsingular on the reduction of $W$ over that residue field; moreover, for any nonsingular affine point $(x_3,y_3)$ of $E$ with $P = (x_3,y_3)$ and $x_3 \in A$, one has $v(x_1-x_2) = v(x_1-x_0)$.
--
--   This is one clause of the additivity of the component map at a place of multiplicative reduction, in the form $c(P_1 - P_2) = 0$ when $P_1$ and $P_2$ have equal level and lie on the same branch of the node: via Tate's uniformisation $c$ is the image in the component group $\mathbb{Z}/n$ of the Néron model of type $I_n$, but here everything is phrased and proved directly with the chord–tangent formulas. It feeds the statements that a torsion point or a suitable multiple lies in the zero component at a prime of multiplicative reduction, and thence the analysis of the Frey curve's $\ell$-division points at such primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.inZeroComponentAt_sub_of_level_eq_of_branch_eq
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₁ y₁)
    (h₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂)
    (hX₁ : A.valuation (x₁ - x₀) < 1) (hX₂ : A.valuation (x₂ - x₀) < 1)
    (hlev : A.valuation (x₁ - x₀) = A.valuation (x₂ - x₀))
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₁ - x₀) ^ 2)
    (hbr : A.valuation ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)) < 1) :
    W.InZeroComponentAt A (.some x₁ y₁ h₁ - .some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : AlgebraicClosure ℚ}
        (h₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
        Point.some x₁ y₁ h₁ - .some x₂ y₂ h₂ = .some x₃ y₃ h₃ → x₃ ∈ A →
          A.valuation (x₁ - x₂) = A.valuation (x₁ - x₀)) := by sorry
