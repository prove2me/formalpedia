-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_rational_verschiebung_of_charP
-- name    : WeierstrassCurve.exists_rational_verschiebung_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/fd2ef7fd-4cb3-57c3-bc51-cc965ecfb58e
-- title:
--   Rational Verschiebung: [p] via F-rational functions of (xᵖ,yᵖ)
-- statement:
--   Let $F$ be a field, let $p$ be a prime with $F$ of characteristic $p$, let $k$ be an algebraically closed field with decidable equality carrying an $F$-algebra structure, and let $W$ be a Weierstrass curve over $F$ that is elliptic. Then there exist four bivariate polynomials $n_X, d_X, n_Y, d_Y \in F[X][Y]$ and a finite set $B \subseteq k$ with the following property: for all $x, y \in k$ such that $(x,y)$ is a nonsingular point of the affine curve obtained by base change of $W$ to $k$, if $x \notin B$ then, writing $f(u,v)$ for the value at $(u,v)$ of the image of $f \in F[X][Y]$ under coefficientwise application of the structure map $F \to k$, one has $d_X(x^p, y^p) \neq 0$ and $d_Y(x^p, y^p) \neq 0$, and the pair $\bigl(n_X(x^p,y^p)/d_X(x^p,y^p),\, n_Y(x^p,y^p)/d_Y(x^p,y^p)\bigr)$ is again a nonsingular point of the base-changed affine curve and equals $p$ times the point $(x,y)$ in the group of affine points.
--
--   This is the statement that multiplication by $p$ on an elliptic curve in characteristic $p$ is inseparable and factors as the $p$-power Frobenius $(x,y) \mapsto (x^p,y^p)$ followed by the Verschiebung, together with the fact that the second factor is given, away from finitely many $x$-coordinates, by rational functions with coefficients in the ground field $F$, without assuming $F$ perfect. It is used in the construction of dual pairs for rational homomorphisms, via [`WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet`](thm.html#WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_rational_verschiebung_of_charP.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_rational_verschiebung_of_charP {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve F) [W.IsElliptic] : ∃ (nX dX nY dY : Polynomial (Polynomial F)) (B : Set k), B.Finite ∧ ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B → WeierstrassCurve.evalEvalBC k dX (x ^ p) (y ^ p) ≠ 0 ∧ WeierstrassCurve.evalEvalBC k dY (x ^ p) (y ^ p) ≠ 0 ∧ ∃ h', p • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some (WeierstrassCurve.evalEvalBC k nX (x ^ p) (y ^ p) / WeierstrassCurve.evalEvalBC k dX (x ^ p) (y ^ p)) (WeierstrassCurve.evalEvalBC k nY (x ^ p) (y ^ p) / WeierstrassCurve.evalEvalBC k dY (x ^ p) (y ^ p)) h' := by sorry
