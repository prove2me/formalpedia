-- Prove2me | Theorems.Thm_WeierstrassCurve_map_veluQuotientOfSums
-- name    : WeierstrassCurve.map_veluQuotientOfSums
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/bd25c587-c6bf-5226-8e3e-a41327106306
-- title:
--   Base change commutes with the Vélu quotient of sums
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $W$ be a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, let $f : R \to R'$ be a ring homomorphism, and let $t, w \in R$. Here $W.\mathrm{veluQuotientOfSums}\,t\,w$ denotes the Weierstrass curve over $R$ whose coefficients are $a_1$, $a_2$, $a_3$, $a_4 - 5t$ and $a_6 - b_2 t - 7w$, where $b_2 = a_1^2 + 4a_2$ is the usual invariant of $W$; and $W.\mathrm{map}\,f$ denotes the Weierstrass curve over $R'$ obtained by applying $f$ to each coefficient. The assertion is the equality of Weierstrass curves over $R'$
--   $$(W.\mathrm{veluQuotientOfSums}\,t\,w).\mathrm{map}\,f = (W.\mathrm{map}\,f).\mathrm{veluQuotientOfSums}\,(f\,t)\,(f\,w),$$
--   that is, forming these modified coefficients commutes with base change along $f$. No hypothesis on $f$ (such as injectivity) is imposed, and no hypothesis relating $t$ and $w$ to torsion data of $W$ is needed.
--
--   This records the naturality under base change of the closed-form Vélu coefficient change, in the shape in which the parameters $t$ and $w$ are given directly rather than as sums over a finite kernel subgroup; it lets a Vélu quotient computed over one ring be compared with the same construction performed after reduction or after passage to a larger ring. It is used in the study of modular curves and their fibre polynomials, where the quotient curve attached to a kernel must be transported along specialisation homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_map_veluQuotientOfSums.lean

import Definitions.Def_WeierstrassCurve_VeluQuotientOfSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.map_veluQuotientOfSums
    {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {R' : Type*} [CommRing R'] (f : R →+* R') (t w : R) :
    (W.veluQuotientOfSums t w).map f = (W.map f).veluQuotientOfSums (f t) (f w) := by sorry
