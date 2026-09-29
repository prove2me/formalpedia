-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_nonsingular_nsmul_eq_zero_and_two_nsmul_ne_zero_of_eval_prePsi_eq_zero
-- name    : WeierstrassCurve.exists_nonsingular_nsmul_eq_zero_and_two_nsmul_ne_zero_of_eval_prePsi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/d16216ef-521c-576f-8095-5657426f771f
-- title:
--   Roots of preΨ'ₙ are abscissae of n-torsion points outside E[2]
-- statement:
--   Let $\Omega$ be an algebraically closed field and let $W$ be a Weierstrass curve over $\Omega$ which is elliptic (its discriminant is a unit). Let $n$ be a natural number whose image in $\Omega$ is non-zero, i.e. $n$ is invertible in $\Omega$, and let $x_0 \in \Omega$ be a root of the univariate primitive $n$-division polynomial `W.preΨ' n` in Mathlib's division-polynomial hierarchy (the factor of the $n$-division polynomial $\psi_n$ obtained by removing the $2$-division factor for even $n$). The assertion is that there exist an element $y_0 \in \Omega$ and a proof $h_0$ that the pair $(x_0, y_0)$ is a nonsingular point of the affine curve attached to $W$, such that the corresponding point `WeierstrassCurve.Affine.Point.some x₀ y₀ h₀` of the group $W(\Omega)$ satisfies both $n \cdot P = O$ and $2 \cdot P \neq O$. Thus every root of the primitive $n$-division polynomial is the abscissa of an $n$-torsion point whose order does not divide $2$; the data $y_0$ and $h_0$ are produced existentially, and the nonsingularity witness is part of the existential statement.
--
--   This is the classical description of the roots of the primitive division polynomial: they are exactly the $x$-coordinates of the points of $E[n]$ lying outside $E[2]$, here in the direction giving a torsion point of order greater than $2$ above each root. It is used to extract points of prescribed exact order from roots of division polynomials, in [`WeierstrassCurve.IsCyclicGenKernel.exists_addOrderOf_eq_and_isRoot`](thm.html#WeierstrassCurve.IsCyclicGenKernel.exists_addOrderOf_eq_and_isRoot) and in the construction of level structures over algebraically closed fields in [`ModularCurve.FullLevel.Diamond.exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_nonsingular_nsmul_eq_zero_and_two_nsmul_ne_zero_of_eval_prePsi_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem WeierstrassCurve.exists_nonsingular_nsmul_eq_zero_and_two_nsmul_ne_zero_of_eval_prePsi_eq_zero
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω) [W.IsElliptic]
    (n : ℕ) (hn : (n : Ω) ≠ 0) (x₀ : Ω) (hx : (W.preΨ' n).eval x₀ = 0) :
    ∃ (y₀ : Ω) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      n • WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ = 0 ∧ 2 • WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ ≠ 0 := by sorry
