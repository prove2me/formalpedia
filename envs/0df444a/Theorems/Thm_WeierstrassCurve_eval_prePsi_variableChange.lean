-- Prove2me | Theorems.Thm_WeierstrassCurve_eval_prePsi_variableChange
-- name    : WeierstrassCurve.eval_prePsi_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/8a5e6f2e-2261-5b2c-ac13-23d0e26a4634
-- title:
--   Univariate division polynomials under a variable change
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve over $R$, let $C = (u, r, s, t)$ be an admissible change of Weierstrass coordinates over $R$ (so $u \in R^{\times}$), let $n \in \mathbb{Z}$ and let $x \in R$. Write $\tilde\psi_n^{W} =$ `W.preΨ n` for Mathlib's univariate division polynomial of $W$, which equals $\psi_n$ for $n$ odd and $\psi_n/\psi_2$ for $n$ even, and let $C \bullet W$ denote the transformed curve `C • W`. The assertion is the identity in $R$
--   $$\tilde\psi_n^{\,C \bullet W}\bigl((u^{-1})^{2}(x - r)\bigr) \;=\; (u^{-1})^{e(n)}\,\tilde\psi_n^{\,W}(x),$$
--   where the image of $u^{-1} \in R^{\times}$ in $R$ is raised to the exponent $e(n) = |n|^{2} - 4$ if $n$ is even and $e(n) = |n|^{2} - 1$ if $n$ is odd, the subtraction being truncated subtraction of natural numbers (so $e(0) = 0$, the corresponding values of $\tilde\psi_n$ on both sides vanishing or being constant). Thus the evaluation of the transformed division polynomial at the transformed abscissa differs from the evaluation of the original one at $x$ by the stated power of $u^{-1}$.
--
--   This is the classical weight table for division polynomials under an admissible coordinate change $x = u^{2}x' + r$, $y = u^{3}y' + u^{2}sx' + t$ (Silverman, Arithmetic of Elliptic Curves, III §1), in the univariate normalisation used by Mathlib. Since the transformation factor is a unit, it shows that the property of being a root of $\tilde\psi_n$ is invariant under coordinate changes; it is used in the analysis of automorphisms of full-level modular curves and of their effect on torsion data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eval_prePsi_variableChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.eval_prePsi_variableChange {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (n : ℤ) (x : R) :
    ((C • W).preΨ n).eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ (n.natAbs ^ 2 - if Even n then 4 else 1) * (W.preΨ n).eval x := by sorry
