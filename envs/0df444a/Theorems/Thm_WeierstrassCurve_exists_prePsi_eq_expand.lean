-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_prePsi_eq_expand
-- name    : WeierstrassCurve.exists_prePsi_eq_expand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/cc2019d4-c39a-53ce-9aa8-d230502fb093
-- title:
--   In characteristic p, ψₚ is a polynomial in xᵖ
-- statement:
--   Let $p$ be a prime number, let $R$ be a commutative ring of characteristic $p$, and let $W$ be a Weierstrass curve over $R$, that is, a tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in R$ presenting the cubic $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$; no smoothness or ellipticity assumption is imposed. Consider the univariate normalised division polynomial $W.\mathrm{pre\Psi}'\,p \in R[X]$, the member of Mathlib's family `preΨ'` indexed by the natural number $p$, which for odd indices $n$ is the $n$-th division polynomial $\psi_n$ of degree $(n^2-1)/2$ and for even indices is its quotient by $\Psi_2 = 2y + a_1x + a_3$. The assertion is that there exists $g \in R[X]$ with $W.\mathrm{pre\Psi}'\,p = \mathrm{expand}\ R\ p\ g$, where `Polynomial.expand R p` is the $R$-algebra endomorphism of $R[X]$ sending $X$ to $X^p$; equivalently, $W.\mathrm{pre\Psi}'\,p$ is $g(X^p)$ for some $g$, so that all of its coefficients in degrees not divisible by $p$ vanish. (For $p = 2$ the polynomial in question is $1$ and the statement is trivial.)
--
--   This is one of the two classical congruences satisfied in characteristic $p$ by the $p$-th division polynomial of a Weierstrass curve, the other identifying its surviving top coefficient with the Hasse invariant. It is used in the proof of Deuring's criterion for supersingularity in the form [`WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero`](thm.html#WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero), which states that the curve has no nontrivial $p$-torsion precisely when the Hasse invariant vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_prePsi_eq_expand.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve

theorem WeierstrassCurve.exists_prePsi_eq_expand {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (W : WeierstrassCurve R) : ∃ g : Polynomial R, W.preΨ' p = Polynomial.expand R p g := by sorry
