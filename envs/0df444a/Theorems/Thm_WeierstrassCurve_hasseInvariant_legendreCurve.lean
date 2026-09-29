-- Prove2me | Theorems.Thm_WeierstrassCurve_hasseInvariant_legendreCurve
-- name    : WeierstrassCurve.hasseInvariant_legendreCurve
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/3d4e3127-2923-59ef-ae79-2e55efc09597
-- title:
--   Hasse invariant of the Legendre curve via the Deuring polynomial
-- statement:
--   Let $R$ be a commutative ring, let $q$ be a natural number which is odd, and let $t \in R$; write $m = (q-1)/2$ (natural subtraction and division). Let `legendreCurve t` be the Weierstrass curve over $R$ with coefficients $a_1 = 0$, $a_2 = -(1+t)$, $a_3 = 0$, $a_4 = t$, $a_6 = 0$, that is $y^2 = x^3 - (1+t)x^2 + tx = x(x-1)(x-t)$, and let `hasseInvariant q` of a Weierstrass curve $W$ over $R$ denote the coefficient of $X^{q-1}$ in the $m$-th power of the polynomial underlying $W$'s two-torsion polynomial, $4X^3 + b_2X^2 + 2b_4X + b_6$. Let `deuringPolynomial q` be the integral polynomial $\sum_{i=0}^{m} \binom{m}{i}^2 X^i$. The assertion is the identity in $R$
--   $$\mathrm{hasseInvariant}_q(\text{legendreCurve } t) \;=\; (-4)^{m}\cdot \Big(\sum_{i=0}^{m}\binom{m}{i}^2 t^i\Big),$$
--   the right-hand side being the evaluation at $t$ of the image of `deuringPolynomial q` under the ring homomorphism $\mathbb{Z} \to R$. No primality of $q$ and no hypothesis on the characteristic of $R$ is required.
--
--   This is the computation of the Hasse invariant of the Legendre family in terms of the Deuring polynomial $\sum_i \binom{m}{i}^2 X^i$, in the normalisation where the invariant is the coefficient of $x^{q-1}$ in $(4x^3+b_2x^2+2b_4x+b_6)^{(q-1)/2}$ (differing from the classical normalisation by the unit $4^{(q-1)/2}$). It is the identity that links the Deuring polynomial to supersingularity in Hasse-invariant form, and it is used in the study of supersingular $j$-invariants and of the Deuring polynomial's behaviour under the $\lambda$-to-$j$ map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_hasseInvariant_legendreCurve.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve

theorem WeierstrassCurve.hasseInvariant_legendreCurve {R : Type*} [CommRing R] {q : ℕ} (hq : Odd q) (t : R) :
    (legendreCurve t).hasseInvariant q
      = (-4) ^ ((q - 1) / 2) * ((Polynomial.deuringPolynomial q).map (Int.castRingHom R)).eval t := by sorry
