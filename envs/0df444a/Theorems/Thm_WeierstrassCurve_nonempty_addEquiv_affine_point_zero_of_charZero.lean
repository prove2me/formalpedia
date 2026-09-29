-- Prove2me | Theorems.Thm_WeierstrassCurve_nonempty_addEquiv_affine_point_zero_of_charZero
-- name    : WeierstrassCurve.nonempty_addEquiv_affine_point_zero_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/76a0db31-16c5-5660-b63c-ad117d4545c3
-- title:
--   Nonsingular points of y²=x³ form Gₐ
-- statement:
--   Let $L$ be a field of characteristic zero, and let $W_0$ be the Weierstrass curve over $L$ with all five coefficients zero, $a_1=a_2=a_3=a_4=a_6=0$, i.e. the cuspidal cubic $y^2=x^3$. The assertion is that the type of additive-group isomorphisms between the point group of the associated affine Weierstrass curve, `(⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve L).toAffine.Point`, and the additive group $(L,+)$ is nonempty; that is, there exists an isomorphism of additive groups $W_0^{\mathrm{ns}}(L) \cong L$. Here the Mathlib point group consists of the point at infinity together with those affine $L$-points of $y^2=x^3$ at which the defining equation is nonsingular (so the cusp $(0,0)$ is excluded), equipped with the chord–tangent addition law and the point at infinity as identity. The statement is an existence statement only: no particular isomorphism is named, and only the additive-group structure, not any further structure, is matched.
--
--   This is the standard identification of the smooth locus of a cuspidal plane cubic with the additive group $\mathbb{G}_a$, in the characteristic-zero case. It is used in the analysis of degenerate Weierstrass curves, where it yields the triviality of $n$-torsion on a cuspidal curve over an algebraically closed field of characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_nonempty_addEquiv_affine_point_zero_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.nonempty_addEquiv_affine_point_zero_of_charZero
    (L : Type*) [Field L] [CharZero L] [DecidableEq L] :
    Nonempty ((⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve L).toAffine.Point ≃+ L) := by sorry
