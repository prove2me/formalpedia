-- Prove2me | Theorems.Thm_WeierstrassCurve_map_veluQuotient_image
-- name    : WeierstrassCurve.map_veluQuotient_image
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/349069b1-7b03-544f-b099-2f5e8aab4ce1
-- title:
--   Vélu's quotient commutes with base change along a ring homomorphism
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $W$ be a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, let $f : R \to R'$ be a ring homomorphism, and let $S$ be a finite set of pairs of elements of $R$ (a Vélu summing set, thought of as a set of coordinate pairs of points). Assume that the image of $S$ under $\mathrm{Prod.map}\ f\ f$, that is under $(x,y) \mapsto (f(x), f(y))$, has the same cardinality as $S$; equivalently, this map is injective on $S$. Writing $\mathrm{veluQuotient}$ for the Weierstrass curve whose first three coefficients are $a_1, a_2, a_3$ and whose remaining coefficients are $a_4 - 5\,t$ and $a_6 - b_2\, t - 7\, w$, where $t$ and $w$ are the sums over the given summing set of the quantities `veluT` and `veluW` attached to each pair, the conclusion is that forming the Vélu quotient and base changing commute: the Vélu quotient of $W \otimes_R R' = W.\mathrm{map}\ f$ along the image set $f(S)$ coincides with the base change along $f$ of the Vélu quotient of $W$ along $S$.
--
--   This is the base-change compatibility of Vélu's formulas for the quotient of a Weierstrass curve by a finite subgroup, stated for an arbitrary ring homomorphism that is merely injective on the summing set, so that it applies to reduction maps $R \to R/\mathfrak{m}$. It is used in the analysis of Tate curves and cyclic quotients, where the reduction of Vélu's model of a quotient curve must be identified with the Vélu quotient of the reduced curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_map_veluQuotient_image.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.map_veluQuotient_image
    {R R' : Type*} [CommRing R] [CommRing R'] [DecidableEq R'] (W : WeierstrassCurve R)
    (f : R →+* R') (S : Finset (R × R))
    (hinj : (S.image (Prod.map f f)).card = S.card) :
    (W.map f).veluQuotient (S.image (Prod.map f f)) = (W.veluQuotient S).map f := by sorry
