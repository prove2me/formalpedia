-- Prove2me | Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
-- name    : WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/6b793040-95f9-52ef-af1a-5b61d2d10cb3
-- title:
--   Equal level, opposite branches: the sum reduces smoothly
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with valuation $v$, and let $x_0,y_0\in A$ satisfy $2y_0+a_1x_0+a_3=0$ and $a_1y_0=3x_0^2+2a_2x_0+a_4$, i.e. $(x_0,y_0)$ is a critical point of $F(x,y)=y^2+a_1xy+a_3y-(x^3+a_2x^2+a_4x+a_6)$, together with $v(b_2+12x_0)=1$ and $v(F(x_0,y_0))<1$. Let $(x_1,y_1)$ and $(x_2,y_2)$ be nonsingular affine points of the base change of $W$ to $\overline{\mathbb{Q}}$ with $v(x_1-x_0)<1$, $v(x_2-x_0)<1$, equal levels $v(x_1-x_0)=v(x_2-x_0)$, shallowness $v(F(x_0,y_0))<v(x_1-x_0)^2$, and slopes on opposite branches: $v\bigl((y_1-y_0)/(x_1-x_0)-(y_2-y_0)/(x_2-x_0)\bigr)=1$. Then, first, the sum $P_1+P_2$ of the two points in the group of $\overline{\mathbb{Q}}$-points satisfies `W.InZeroComponentAt A`, that is, either it is the point at infinity, or it is an affine point $(x,y)$ with $x\notin A$, or it is an affine point with $x,y\in A$ whose residues give a nonsingular point of the reduction of $W$ over the residue field of $A$; and second, whenever $P_1+P_2$ equals an affine nonsingular point $(x_3,y_3)$ with $x_3\in A$, one has $v(x_1-x_2)=v(x_1-x_0)$.
--
--   This is one clause of the signed-level calculus at a place of multiplicative reduction: in the Tate-curve dictionary, where the level $v(x-x_0)$ and the branch of a point reducing to the node compute its image in the component group $\mathbb{Z}/n$ of a Néron model of type $I_n$, it records that two shallow points of equal level on opposite branches have opposite components, so their sum lies in the identity component. It is used in the analysis of the Frey curve's local behaviour, for instance in [`WeierstrassCurve.exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor`](thm.html#WeierstrassCurve.exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor) and in the component-group arguments for Frey packages.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne
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
    (hbr : A.valuation ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)) = 1) :
    W.InZeroComponentAt A (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : AlgebraicClosure ℚ}
        (h₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
        Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ = .some x₃ y₃ h₃ → x₃ ∈ A →
          A.valuation (x₁ - x₂) = A.valuation (x₁ - x₀)) := by sorry
