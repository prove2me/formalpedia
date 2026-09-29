-- Prove2me | Theorems.Thm_P2M_Dup_WeierstrassCurve_ellipticNet_four
-- name    : P2M.Dup.WeierstrassCurve.ellipticNet_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/12e6c1a1-01ae-55a6-b0f4-e8b4eab25275
-- title:
--   Elliptic-net identity at index 4
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, and $t$ an element of $R$. Write $\Phi_n$ and $\Psi^{[2]}_n$ for Mathlib's reduced division polynomials `WeierstrassCurve.Φ` and `WeierstrassCurve.ΨSq` of $W$, and $b_2, b_4, b_6$ for the standard invariants `W.b₂`, `W.b₄`, `W.b₆`. The theorem asserts the identity in $R$ obtained by evaluating these polynomials at $t$:
--   $$2t\,\Phi_4(t)\bigl(\Phi_4(t)+t\,\Psi^{[2]}_4(t)\bigr)+b_2\,t\,\Phi_4(t)\Psi^{[2]}_4(t)+b_4\bigl(\Phi_4(t)+t\,\Psi^{[2]}_4(t)\bigr)\Psi^{[2]}_4(t)+b_6\,\Psi^{[2]}_4(t)^2=\Phi_5(t)\Psi^{[2]}_3(t)+\Phi_3(t)\Psi^{[2]}_5(t).$$
--   No hypotheses beyond commutativity of $R$ are imposed: the identity holds for every Weierstrass curve over every commutative ring and every $t$, being a polynomial identity in $t$ and the coefficients of $W$.
--
--   This is the instance at index $m=4$ of the symmetric-addition (elliptic net) relation expressing the compatibility of $x\mapsto \Phi_m(x)/\Psi^{[2]}_m(x)$ with the addition law on $W$, here in the homogeneous form that avoids denominators. It serves as a base case, together with the small-index instances, for the induction proving $x(mP)\,\Psi^{[2]}_m(x(P))=\Phi_m(x(P))$ for multiples of a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_ellipticNet_four.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DivPolyMulFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem P2M.Dup.WeierstrassCurve.ellipticNet_four {R : Type*} [CommRing R] (W : WeierstrassCurve R) (t : R) :
    2 * t * (W.Φ 4).eval t * ((W.Φ 4).eval t + t * (W.ΨSq 4).eval t) +
        W.b₂ * t * ((W.Φ 4).eval t * (W.ΨSq 4).eval t) +
        W.b₄ * (((W.Φ 4).eval t + t * (W.ΨSq 4).eval t) * (W.ΨSq 4).eval t) +
        W.b₆ * (W.ΨSq 4).eval t ^ 2 =
      (W.Φ 5).eval t * (W.ΨSq 3).eval t + (W.Φ 3).eval t * (W.ΨSq 5).eval t := by sorry
