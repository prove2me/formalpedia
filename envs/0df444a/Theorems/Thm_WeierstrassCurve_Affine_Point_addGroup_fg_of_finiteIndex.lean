-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex
-- name    : WeierstrassCurve.Affine.Point.addGroup_fg_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/fefdd496-d8d6-560c-bbc1-b2f89d7dd56e
-- title:
--   Descent: 2E(ℚ) of finite index implies E(ℚ) finitely generated
-- statement:
--   Let $W$ be an affine Weierstrass curve over $\mathbb{Q}$, that is, a tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in \mathbb{Q}$ presenting the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$, and let $W(\mathbb{Q})$ denote the Mordell–Weil group `W.Point`, whose elements are the point at infinity together with the nonsingular rational solutions of that equation, with the usual chord–tangent addition. Assume first that the discriminant of $W$ is nonzero, $\Delta \neq 0$, so that $W$ is an elliptic curve. Assume second that the image of the doubling endomorphism $P \mapsto 2P$ of $W(\mathbb{Q})$, taken as the range of the additive monoid homomorphism `nsmulAddMonoidHom 2`, has finite index in $W(\mathbb{Q})$, i.e. $[W(\mathbb{Q}) : 2W(\mathbb{Q})] < \infty$. The conclusion is that $W(\mathbb{Q})$ is finitely generated as an additive group. Only the case $n = 2$ of the finite-index hypothesis is assumed, and that hypothesis is taken as given: the assertion is the descent step alone, not the weak Mordell–Weil theorem.
--
--   This is the descent half of the Mordell–Weil theorem over $\mathbb{Q}$: finiteness of $W(\mathbb{Q})/2W(\mathbb{Q})$ plus the theory of naive heights gives finite generation, so that for a particular curve the Mordell–Weil theorem is reduced to an explicit $2$-descent. It is used in the analysis of rational points on the elliptic curve of conductor $15$ occurring in the determination of the rational points of the relevant modular curve, through [`ModularCurve.FifteenA1.coords_of_equation`](thm.html#ModularCurve.FifteenA1.coords_of_equation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.Point.addGroup_fg_of_finiteIndex (W : WeierstrassCurve.Affine ℚ) (hΔ : W.Δ ≠ 0) (hweak : (nsmulAddMonoidHom 2 : W.Point →+ W.Point).range.FiniteIndex) : AddGroup.FG W.Point := by sorry
