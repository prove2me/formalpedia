-- Prove2me | Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
-- name    : WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/262dfa48-cac6-5f2f-8904-5a034c2afd21
-- title:
--   Off the zero component iff the abscissa meets the node
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, with coefficients $a_1,a_2,a_3,a_4,a_6$ and $b_2 = a_1^2 + 4a_2$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, with its multiplicative valuation $v_A$ (so $v_A(t) = 1$ means $t \in A^{\times}$ and $v_A(t) < 1$ means $t$ lies in the maximal ideal of $A$). Let $x_0, y_0 \in A$ satisfy the two critical-point equations $2y_0 + a_1x_0 + a_3 = 0$ and $a_1y_0 = 3x_0^2 + 2a_2x_0 + a_4$, suppose $b_2 + 12x_0$ is a unit of $A$, i.e. $v_A(b_2 + 12x_0) = 1$, and suppose $v_A\bigl(y_0^2 + a_1x_0y_0 + a_3y_0 - (x_0^3 + a_2x_0^2 + a_4x_0 + a_6)\bigr) < 1$, so that $(x_0,y_0)$ reduces to a singular point of the reduction of $W$. Let $x, y \in \overline{\mathbb{Q}}$ be the coordinates of a nonsingular affine point of $W$ base changed to $\overline{\mathbb{Q}}$ (via $\mathbb{Z} \to \mathbb{Q}$). Then the point $(x,y)$ fails to satisfy `InZeroComponentAt` for $A$ — that is, it is neither the point at infinity, nor has $x \notin A$, nor has $x, y \in A$ with residues giving a nonsingular point of $W$ over the residue field of $A$ — if and only if $v_A(x - x_0) < 1$.
--
--   This is the dictionary, in node-centred coordinates, between the filtration subgroup of points with nonsingular reduction at a place of multiplicative reduction and the condition that the abscissa reduces to that of the node. It is used in the analysis of inertia at primes dividing $abc$ acting on the $p$-torsion of a Frey curve, and is cited by the Frey-package lemmas on inertial branches and fixed points at such primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y) :
    ¬ W.InZeroComponentAt A (.some x y h) ↔ A.valuation (x - x₀) < 1 := by sorry
