-- Prove2me | Theorems.Thm_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
-- name    : WeierstrassCurve.Psi2Sq_mul_wronskian_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c0ea395f-0545-5f87-a6fd-bc24ddf82f1e
-- title:
--   Wronskian identity for division polynomials: [n]^*ω = n ω
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, given by coefficients $a_1,a_2,a_3,a_4,a_6$ with no nonsingularity assumption, and let $n$ be an integer. Write $\Phi_n$ and $\Psi^{\mathrm{sq}}_n$ for the polynomials in $R[X]$ that serve as numerator and denominator of the abscissa of multiplication by $n$, $\Psi_2^{\mathrm{sq}} = 4X^3 + b_2X^2 + 2b_4X + b_6$ for the square of the $2$-division polynomial, $C$ for the inclusion of constants and $'$ for the formal derivative on $R[X]$. The assertion is the identity in $R[X]$
--   $$\Psi_2^{\mathrm{sq}}\cdot\bigl(\Phi_n'\,\Psi^{\mathrm{sq}}_n - \Phi_n\,(\Psi^{\mathrm{sq}}_n)'\bigr)^2 = (n\cdot 1_R)^2\cdot \Psi^{\mathrm{sq}}_n\bigl(4\Phi_n^3 + b_2\,\Phi_n^2\,\Psi^{\mathrm{sq}}_n + 2b_4\,\Phi_n\,(\Psi^{\mathrm{sq}}_n)^2 + b_6\,(\Psi^{\mathrm{sq}}_n)^3\bigr),$$
--   where $n$ acts through its image in $R$ and $b_2,b_4,b_6$ are the usual invariants of $W$. The bracket on the right is the homogenisation of $\Psi_2^{\mathrm{sq}}$ evaluated at $\Phi_n/\Psi^{\mathrm{sq}}_n$, i.e. $(\Psi^{\mathrm{sq}}_n)^3\,\Psi_2^{\mathrm{sq}}(\Phi_n/\Psi^{\mathrm{sq}}_n)$.
--
--   This is the relation $[n]^*\omega = n\,\omega$ for the invariant differential $\omega = dx/(2y + a_1x + a_3)$, recast as a polynomial identity over an arbitrary base by squaring and clearing denominators, the Wronskian $\Phi_n'\Psi^{\mathrm{sq}}_n - \Phi_n(\Psi^{\mathrm{sq}}_n)'$ being $(\Psi^{\mathrm{sq}}_n)^2$ times the derivative of the abscissa of $[n]$. It feeds the later analysis of division polynomials and of $n$-torsion on Weierstrass curves, for instance the identification of a coefficient of the division polynomial with the Hasse invariant and the study of rational points in the Čerednik–Drinfel'd material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve

theorem WeierstrassCurve.Psi2Sq_mul_wronskian_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) : W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2 = C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3)) := by sorry
