-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
-- name    : WeierstrassCurve.Affine.Point.eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/fffc803d-471c-50bd-8ebd-100cc59a3b73
-- title:
--   Roots of the reduced n-division polynomial
-- statement:
--   Let $F$ be a field with decidable equality and let $W$ be a Weierstrass curve over $F$ which is elliptic, i.e. whose discriminant is invertible. Let $n$ be a natural number whose image in $F$ is nonzero (so in particular $n \neq 0$ and the characteristic of $F$ does not divide $n$), and let $x, y \in F$ be such that $(x,y)$ is a nonsingular point of the affine Weierstrass curve $W$; write $P$ for the corresponding element `WeierstrassCurve.Affine.Point.some x y h` of the group of points of the affine curve, whose zero is the point at infinity. The assertion is an equivalence: the $n$-th reduced (univariate) division polynomial $\mathrm{pre}\Psi'_n \in F[X]$ of $W$ vanishes at $x$ if and only if $n \cdot P = 0$ and $2 \cdot P \neq 0$, the multiples being taken with respect to the natural-number scalar action on the group of points. Thus the roots of $\mathrm{pre}\Psi'_n$ in $F$ are exactly the abscissae of those $F$-points of $W$ that are $n$-torsion but not $2$-torsion; for even $n$ this excludes the abscissae of the nontrivial $2$-torsion points.
--
--   This is the classical description of the roots of the reduced division polynomial (for odd $n$ the usual criterion $\psi_n(x(P)) = 0 \iff nP = O$, with the even case recording that the $2$-torsion abscissae are removed). It is used when reading $\Gamma_0(2^k)$-level structures in generator-and-kernel form, where the condition that a point have exact order a power of $2$ becomes a divisibility between reduced division polynomials of even index, and in the attendant statements about modular curves of full and $\Gamma_1$ level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.Affine.Point.eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : (n : F) ≠ 0) {x y : F} (h : W.toAffine.Nonsingular x y) :
    (W.preΨ' n).eval x = 0 ↔
      n • WeierstrassCurve.Affine.Point.some x y h = 0 ∧ 2 • WeierstrassCurve.Affine.Point.some x y h ≠ 0 := by sorry
