-- Prove2me | Theorems.Thm_WeierstrassCurve_two_mul_omega
-- name    : WeierstrassCurve.two_mul_omega
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/b88832ee-7060-5ba4-b19e-cddb7a12ba5b
-- title:
--   ωₙ is an exact half of 2ωₙ
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve over $R$ (given by its coefficients $a_1,a_2,a_3,a_4,a_6$), and let $n$ be an integer. The theorem asserts the identity $2\,\omega_n = (2\omega)_n$ in the bivariate polynomial ring $R[X][Y]$, that is, `2 * W.ω n = W.twoω n`, where `W.twoω n` is the project's explicit bivariate polynomial playing the role of $2\omega_n$ (built from the division polynomials $\psi$, $\phi$ and the doubling polynomial attached to $W$, with no reduction modulo the Weierstrass equation) and `W.ω n` is the project's $\omega_n$, obtained by halving the integer coefficients of the corresponding polynomial for the universal Weierstrass curve over $\mathbb{Z}[A_1,A_2,A_3,A_4,A_6]$ and then specialising $A_i \mapsto a_i$. Thus the content is that this coefficientwise halving is exact: doubling the result returns `W.twoω n`, over every commutative ring, for every integer $n$ (no positivity, invertibility or characteristic hypothesis).
--
--   This legitimises the definition of the division polynomial $\omega_n$ of a Weierstrass curve over an arbitrary base, by confirming that the polynomial denoted $2\omega_n$ really has even coefficients universally, so that $\omega_n$ is its exact half; classically $\omega_n$ is the $y$-coordinate numerator in $[n]P = (\phi_n/\psi_n^2, \omega_n/\psi_n^3)$. It is used in the construction of a rational Verschiebung in characteristic $p$ ([`WeierstrassCurve.exists_rational_verschiebung_of_charP`](thm.html#WeierstrassCurve.exists_rational_verschiebung_of_charP)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_two_mul_omega.lean

import Definitions.Def_EllipticCurve_DivisionPolynomialOmega

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.two_mul_omega {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) : 2 * W.ω n = W.twoω n := by sorry
