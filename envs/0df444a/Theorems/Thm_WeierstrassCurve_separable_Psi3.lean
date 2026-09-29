-- Prove2me | Theorems.Thm_WeierstrassCurve_separable_Psi3
-- name    : WeierstrassCurve.separable_Psi3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/9c13147a-b222-5410-b45b-9bf602e61feb
-- title:
--   Separability of Ψ₃ for a nonsingular Weierstrass curve
-- statement:
--   Let $K$ be a field in which $3 \neq 0$, and let $W$ be a Weierstrass curve over $K$, that is, a tuple of coefficients $a_1, a_2, a_3, a_4, a_6$, whose discriminant $\Delta(W)$ is assumed nonzero. The assertion is that the polynomial $\Psi_3(W) = 3X^4 + b_2X^3 + 3b_4X^2 + 3b_6X + b_8 \in K[X]$, formed from the usual quantities $b_2, b_4, b_6, b_8$ attached to $W$, is separable in the sense of Mathlib's `Polynomial.Separable`: it is coprime to its formal derivative, i.e. there exist $u, v \in K[X]$ with $u\,\Psi_3 + v\,\Psi_3' = 1$. No hypothesis of characteristic other than $3 \neq 0$ is imposed, and the Weierstrass equation is the general five-coefficient one rather than a short model. Since $\Psi_3$ has degree $4$ when $3 \neq 0$, the conclusion says equivalently that $\Psi_3$ has four distinct roots in an algebraic closure of $K$, these being the $x$-coordinates of the eight points of exact order $3$ on the associated elliptic curve.
--
--   This is the classical statement that the $x$-coordinates of the $3$-torsion points of a nonsingular elliptic curve are pairwise distinct away from characteristic $3$. It is used in the specialisation argument producing a curve in a one-parameter family whose $3$-division polynomial has no root, in [`WeierstrassCurve.exists_forall_not_isRoot_Psi3_specialization`](thm.html#WeierstrassCurve.exists_forall_not_isRoot_Psi3_specialization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_separable_Psi3.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Separable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.separable_Psi3 {K : Type*} [Field K] (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (h3 : (3 : K) ≠ 0) : W.Ψ₃.Separable := by sorry
