-- Prove2me | Theorems.Thm_TateCurve_nnnorm_Delta
-- name    : TateCurve.nnnorm_Delta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ce400f53-ffdd-5fc0-ad99-5369eb2ac058
-- title:
--   Tate curve discriminant has norm ‖q‖
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $q \in K$. Assume $q \neq 0$ and $\|q\|_+ < 1$, the norm being taken in the nonnegative-reals-valued form $\|\cdot\|_+$. Write `curve q` for the Weierstrass curve over $K$ with coefficients $a_1 = 1$, $a_2 = 0$, $a_3 = 0$ and $a_4 =$ `a₄ q`, $a_6 =$ `a₆ q`, that is, $y^2 + xy = x^3 + a_4(q)x + a_6(q)$, where `a₄` and `a₆` are the $q$-series coefficients of the Tate curve; and let $\Delta$ denote Mathlib's discriminant of a Weierstrass curve, applied to this curve. The assertion is the equality of nonnegative real numbers $\|\Delta(\mathrm{curve}\ q)\|_+ = \|q\|_+$. Only the norm of the discriminant is asserted; no product expansion of $\Delta$ is claimed.
--
--   This is the first of the three norm computations ($\|\Delta\| = \|q\|$, $\|c_4\| = 1$, $\|j\| = \|q\|^{-1}$) expressing that the Tate curve $E_q$ has multiplicative reduction, the normed form of the classical identity $\Delta(E_q) = q\prod_{n \ge 1}(1 - q^n)^{24}$. It is used in the identification of the twisting parameter of the Tate curve, via [`TateCurve.nnnorm_twistParam_curve_eq_one`](thm.html#TateCurve.nnnorm_twistParam_curve_eq_one), en route to recognising the Frey curve at a prime dividing $abc$ as a Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_nnnorm_Delta.lean

import Definitions.Def_TateCurve_QSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve NNReal
open scoped NNReal
namespace TateCurve
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K}

theorem nnnorm_Delta (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : ‖(curve q).Δ‖₊ = ‖q‖₊ := by sorry
