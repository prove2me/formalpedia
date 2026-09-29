-- Prove2me | Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_antipodal
-- name    : WeierstrassCurve.inZeroComponentAt_add_of_antipodal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/f845408c-ceb5-599f-9bb4-b8050576e242
-- title:
--   Sum of two antipodal points at a node lies in E⁰
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with valuation $v$, and write $E$ for the base change to $\overline{\mathbb{Q}}$ of $W$ viewed over $\mathbb{Q}$. Fix $x_0,y_0\in A$ satisfying the two partial-derivative relations $2y_0+a_1x_0+a_3=0$ and $a_1y_0=3x_0^2+2a_2x_0+a_4$, so that $(x_0,y_0)$ is a critical point of $F(x,y)=y^2+a_1xy+a_3y-(x^3+a_2x^2+a_4x+a_6)$, and assume $v(b_2+12x_0)=1$ (i.e. $b_2+12x_0$ is a unit of $A$) together with $v(F(x_0,y_0))<1$ (i.e. $F_0:=F(x_0,y_0)$ lies in the maximal ideal). Let $(x_1,y_1)$ and $(x_2,y_2)$ be nonsingular affine points of $E$ such that $v(x_i-x_0)<1$ and $v(x_i-x_0)^2\le v(F_0)$ for $i=1,2$. Then the sum $(x_1,y_1)+(x_2,y_2)$ in the group of points of $E$ satisfies $W.\mathrm{InZeroComponentAt}\,A$: it is either the point at infinity, or an affine point $(x,y)$ for which $x\notin A$, or an affine point with $x,y\in A$ whose residues in the residue field of $A$ form a nonsingular point of the reduction of $W$.
--
--   This is one clause of the additivity, at a place of multiplicative reduction, of the map sending a point reducing to the node to its component in the special fibre: two points of "antipodal" level, each of component class $n/2$ in the Tate parametrisation, add up into the identity component. It feeds the results constructing points in the identity component used in the filtration arguments at primes of multiplicative reduction, via [`WeierstrassCurve.node_chord_trichotomy`](thm.html#WeierstrassCurve.node_chord_trichotomy) and [`WeierstrassCurve.inZeroComponentAt_of_valuation_sub_eq_one`](thm.html#WeierstrassCurve.inZeroComponentAt_of_valuation_sub_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_add_of_antipodal.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.inZeroComponentAt_add_of_antipodal
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
    (hX₁ : A.valuation (x₁ - x₀) < 1)
    (hanti₁ : A.valuation (x₁ - x₀) ^ 2 ≤ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)))
    (hX₂ : A.valuation (x₂ - x₀) < 1)
    (hanti₂ : A.valuation (x₂ - x₀) ^ 2 ≤ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) :
    W.InZeroComponentAt A (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) := by sorry
