-- Prove2me | Theorems.Thm_TateCurve_nnnorm_c4
-- name    : TateCurve.nnnorm_c4
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/13e755b8-5a5f-5375-99ad-1b3535635da4
-- title:
--   ‖c₄‖=1 for the Tate curve
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $q \in K$. The curve attached to $q$ is the Weierstrass curve `curve q` over $K$ with coefficients $a_1 = 1$, $a_2 = a_3 = 0$ and $a_4 =$ `a₄ q`, $a_6 =$ `a₆ q`, the two latter being the $q$-series coefficients of the Tate parametrisation. Under the hypothesis $\|q\|_+ < 1$ on the (nonnegative-real-valued) norm of $q$, the assertion is that the invariant $c_4$ of this Weierstrass curve has norm exactly $1$: $\|(\,$`curve q`$)\mathord{.}c_4\|_+ = 1$. For these coefficients $b_2 = a_1^2 + 4a_2 = 1$ and $b_4 = 2a_4 + a_1 a_3 = 2\,$`a₄ q`, so that $c_4 = b_2^2 - 24 b_4 = 1 - 48\,$`a₄ q`; the statement therefore says that this element of $K$ is a unit of norm one, for every $q$ in the open unit disc.
--
--   This is the standard fact that the Tate curve $E_q$ has $|c_4| = 1$, hence (together with $\|\Delta\| = \|q\|$) multiplicative rather than additive reduction. It is used in the normalisation of the twisting parameter of the Tate curve, via [`TateCurve.nnnorm_twistParam_curve_eq_one`](thm.html#TateCurve.nnnorm_twistParam_curve_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_nnnorm_c4.lean

import Definitions.Def_TateCurve_QSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve NNReal
open scoped NNReal
namespace TateCurve
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K}

theorem nnnorm_c4 (hq : ‖q‖₊ < 1) : ‖(curve q).c₄‖₊ = 1 := by sorry
