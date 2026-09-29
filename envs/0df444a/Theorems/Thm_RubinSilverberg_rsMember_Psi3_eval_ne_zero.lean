-- Prove2me | Theorems.Thm_RubinSilverberg_rsMember_Psi3_eval_ne_zero
-- name    : RubinSilverberg.rsMember_Psi3_eval_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/6f00029b-75cb-5e06-a448-bf5144bc4d1d
-- title:
--   No K(X)-rational 3-division point on the generic Rubin–Silverberg curve
-- statement:
--   Let $K$ be a field of characteristic $0$, let $\zeta \in K$ be a primitive fifth root of unity, and let $a, b, u_0 \in K$ with $a \neq 0$ and $b \neq 0$ satisfy `IsKleinDatum a b u₀`, that is $H(u_0)^3(4a^3 + 27b^2) + 6912\,a^3 V(u_0)^5 = 0$ together with $V(u_0) \neq 0$, where $H(u) = u^{20} - 228u^{15} + 494u^{10} + 228u^5 + 1$ and $V(u) = u(u^{10} + 11u^5 - 1)$. Let $\lambda \in K$ be arbitrary. Consider the generic member of the Rubin–Silverberg family over the rational function field $K(X)$: the Weierstrass curve $y^2 = x^3 + Ax + B$ with $A = a\,\mathrm{kleinHHom}(N, D)/H(u_0)$ and $B = b\,\mathrm{kleinTHom}(N, D)/T(u_0)$, where $N$ and $D$ are the quantities `rsNum`, `rsDen` evaluated at the constants $u_0$, $\lambda$ and at the parameter $t = X$, all coefficients being taken as the constant rational functions $C a$, $C b$, $C u_0$, $C \lambda$. The assertion is that the third division polynomial $\Psi_3$ of this curve, a polynomial over $K(X)$, takes a nonzero value at every $x \in K(X)$; equivalently, it has no root in $K(X)$.
--
--   This says that the generic fibre of the Rubin–Silverberg family, whose mod-$5$ representation is constant by construction, has no $K(X)$-rational point of order dividing $3$ in the $x$-coordinate sense, and thus supplies the non-vanishing input for the mod-$3$ statements about the family. It is obtained by transporting the corresponding statement for Klein's curve `kleinCurve` along the Möbius substitution $X \mapsto N/D$, which is an automorphism of $K(X)$, and it is used by [`RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily`](thm.html#RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_rsMember_Psi3_eval_ne_zero.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.rsMember_Psi3_eval_ne_zero {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K} (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum a b u₀) (l : K) (x : RatFunc K) : ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 := by sorry
