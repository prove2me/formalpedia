-- Prove2me | Theorems.Thm_WeierstrassCurve_fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
-- name    : WeierstrassCurve.fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/c9bbb43b-f583-5df7-a31b-81cab6368d60
-- title:
--   Tower law for Vélu full-kernel quotient Weierstrass models
-- statement:
--   Let $K$ be an algebraically closed field with decidable equality, $W$ a Weierstrass curve over $K$ whose discriminant is invertible (so $W$ is elliptic), and $d,m$ nonzero natural numbers with $(dm : K)\neq 0$. Let $Q$ be a point of the affine model of $W$ with $\operatorname{addOrderOf} Q = dm$, and put $T = m\cdot Q$. Here, for a point $R$ and a level $N$, `W.fullKernelQuotient R N` is the Weierstrass curve with the same $a_1,a_2,a_3$ as $W$, with $a_4$ replaced by $a_4 - 5t$ and $a_6$ by $a_6 - b_2 t - 7w$, where $t=\sum g_x(x,y)$ and $w=\sum\bigl(x\,g_x(x,y)-y\,g_y(x,y)\bigr)$, the sums running over the finite set of coordinate pairs $(x,y)$ of the points $k\cdot R$ for $1\le k\le N-1$ (the point at infinity contributing $(0,0)$), with $g_x = 3x^2+2a_2x+a_4-a_1y$ and $g_y=-(2y+a_1x+a_3)$. Assume given an additive homomorphism $\varphi$ from the points of $W$ to the points of `W.fullKernelQuotient T d` whose kernel is the subgroup of integer multiples of $T$ and which, on every point $P$ outside that subgroup, is given by Vélu's translation sums $\bigl(x(P)+\sum_{k=1}^{d-1}(x(P+kT)-x(kT)),\; y(P)+\sum_{k=1}^{d-1}(y(P+kT)-y(kT))\bigr)$, coordinates of the point at infinity again read as $(0,0)$. The conclusion is an equality of Weierstrass curves over $K$, that is of all five coefficients: the level-$m$ full-kernel quotient of `W.fullKernelQuotient T d` at the point $\varphi(Q)$ equals `W.fullKernelQuotient Q (d*m)`.
--
--   This is the compositionality (tower) statement for Vélu's explicit quotient models: quotienting $W$ by $\langle mQ\rangle$ and then by the image of $Q$ produces, coefficient by coefficient, the same Weierstrass equation as quotienting $W$ by $\langle Q\rangle$ in one step. It is used in the comparison of $j$-invariants of cyclic quotients and in the analysis of moduli points on modular curves, notably in connection with Atkin–Lehner involutions and $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] {d m : ℕ} [NeZero d] [NeZero m]
    (hN : ((d * m : ℕ) : K) ≠ 0) (Q : W.toAffine.Point) (hQ : addOrderOf Q = d * m)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient (m • Q) d).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples (m • Q))
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples (m • Q) →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (d - 1),
            ((P + k • (m • Q)).coordsOrZero.1 - (k • (m • Q)).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (d - 1),
            ((P + k • (m • Q)).coordsOrZero.2 - (k • (m • Q)).coordsOrZero.2))) :
    (W.fullKernelQuotient (m • Q) d).fullKernelQuotient (φ Q) m = W.fullKernelQuotient Q (d * m) := by sorry
