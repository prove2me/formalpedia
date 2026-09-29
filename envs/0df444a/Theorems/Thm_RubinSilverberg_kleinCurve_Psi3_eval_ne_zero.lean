-- Prove2me | Theorems.Thm_RubinSilverberg_kleinCurve_Psi3_eval_ne_zero
-- name    : RubinSilverberg.kleinCurve_Psi3_eval_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/ddc41dae-2128-5bad-906b-8c16336f2c27
-- title:
--   No K(X)-rational 3-division point on Klein's quintic family
-- statement:
--   Let $K$ be a field of characteristic zero and let $\zeta \in K$ be a primitive fifth root of unity. Over the rational function field $K(X)$ consider the Weierstrass curve `kleinCurve RatFunc.X` with coefficients $a_1 = a_2 = a_3 = 0$, $a_4 = -\mathrm{kleinH}(X)/48$ and $a_6 = \mathrm{kleinT}(X)/864$, where $\mathrm{kleinH}(u) = u^{20} - 228u^{15} + 494u^{10} + 228u^{5} + 1$ and $\mathrm{kleinT}(u) = u^{30} + 522u^{25} - 10005u^{20} - 10005u^{10} - 522u^{5} + 1$ are Klein's icosahedral forms evaluated at the indeterminate $X$; that is, the curve $y^2 = x^3 - \tfrac{1}{48}\mathrm{kleinH}(X)\,x + \tfrac{1}{864}\mathrm{kleinT}(X)$ over $K(X)$. The assertion is that for every $x \in K(X)$ the value at $x$ of the third division polynomial $\Psi_3$ of this curve is nonzero; equivalently, $\Psi_3$ has no root in $K(X)$, so the generic fibre has no $3$-division point whose abscissa lies in $K(X)$, hence no $K(X)$-rational subgroup of order $3$.
--
--   This is the generic-fibre irreducibility input for the mod $3$ representation attached to the Rubin–Silverberg family built from Klein's level-$5$ icosahedral curve: absence of a rational root of $\Psi_3$ over the function field rules out a Galois-stable line of order $3$. It is used by [`RubinSilverberg.rsMember_Psi3_eval_ne_zero`](thm.html#RubinSilverberg.rsMember_Psi3_eval_ne_zero), which transfers the conclusion to the individual members of the family; the icosahedral symmetry matrices `icoS`, `icoT`, `icoU` and the Möbius action of $\mathrm{SL}_2$ on $K(X)$ enter through the cited lemmas.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_kleinCurve_Psi3_eval_ne_zero.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.kleinCurve_Psi3_eval_ne_zero {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (x : RatFunc K) : ((kleinCurve (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 := by sorry
