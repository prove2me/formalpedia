-- Prove2me | Theorems.Thm_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant
-- name    : WeierstrassCurve.coeff_prePsi_eq_hasseInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/4f4f73c0-9266-5935-ae75-4c8b24a519e6
-- title:
--   Coefficient of x^{p(p-1)/2} in ψₚ is the Hasse invariant
-- statement:
--   Let $R$ be a commutative ring, let $p$ be a prime natural number with $p \neq 2$, assume $R$ has characteristic $p$, and let $W$ be a Weierstrass curve over $R$, given by a cubic $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ with coefficients in $R$; no smoothness or ellipticity hypothesis is imposed. Write $\mathrm{pre}\Psi'_n \in R[x]$ for the normalised univariate division polynomials of $W$, so that for odd $n$ the polynomial $\mathrm{pre}\Psi'_n$ is the $n$-th division polynomial $\psi_n$ itself. The assertion is that the coefficient of $x^{p\cdot\lfloor (p-1)/2\rfloor} = x^{p(p-1)/2}$ in $\mathrm{pre}\Psi'_p$ equals the Hasse invariant of $W$ at $p$, which is by definition the coefficient of $x^{p-1}$ in the $\lfloor (p-1)/2 \rfloor$-th power of the two-torsion cubic of $W$, i.e.
--   $$\bigl[x^{p(p-1)/2}\bigr]\,\psi_p \;=\; \bigl[x^{p-1}\bigr]\,\bigl(4x^3 + b_2x^2 + 2b_4x + b_6\bigr)^{(p-1)/2} \quad\text{in } R.$$
--   Here the exponents are computed with natural-number subtraction and division, which for odd $p$ agree with the usual values.
--
--   This is the identity of Gunji and Debry identifying a single coefficient of the $p$-th division polynomial in characteristic $p$ with the Hasse invariant. It is used to prove that the $p$-torsion of an elliptic curve over a field of characteristic $p$ is annihilated identically exactly when the Hasse invariant vanishes, the supersingularity criterion [`WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero`](thm.html#WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve

theorem WeierstrassCurve.coeff_prePsi_eq_hasseInvariant {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) [CharP R p] (W : WeierstrassCurve R) : (W.preΨ' p).coeff (p * ((p - 1) / 2)) = W.hasseInvariant p := by sorry
