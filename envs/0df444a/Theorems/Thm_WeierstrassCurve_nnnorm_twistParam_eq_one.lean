-- Prove2me | Theorems.Thm_WeierstrassCurve_nnnorm_twistParam_eq_one
-- name    : WeierstrassCurve.nnnorm_twistParam_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/f3908168-e2ad-517e-af99-1b9ae3178890
-- title:
--   Unit twist parameter for two multiplicative-reduction curves
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is non-archimedean (an ultrametric distance), and let $E$ and $E'$ be Weierstrass curves over $K$, with $c_4$, $c_6$ and $\Delta$ the usual invariants attached to their coefficients. Assume that the non-negative real norms of the invariants of $E$ satisfy $\|c_4(E)\|=1$ and $\|\Delta(E)\|<1$, and likewise for $E'$, namely $\|c_4(E')\|=1$ and $\|\Delta(E')\|<1$ (the normalisation expressing multiplicative reduction). The conclusion is that the element
--   $$d=\frac{c_6(E)\,c_4(E')}{c_6(E')\,c_4(E)}\in K$$
--   has norm $\|d\|=1$. Norms are taken in the `NNReal`-valued form $\|\cdot\|_{+}$, and the quotient is the field division in $K$; no separate nonvanishing hypothesis on the denominator is imposed, the hypotheses already forcing $c_6(E')$ and $c_4(E)$ to be units for the norm.
--
--   This is the valuation criterion behind the comparison of two curves with multiplicative reduction by a quadratic twist: the twist parameter $d$ is a norm-one element, so that $K(\sqrt{d})$ is at most an unramified quadratic extension of $K$. It is used by [`TateCurve.nnnorm_twistParam_curve_eq_one`](thm.html#TateCurve.nnnorm_twistParam_curve_eq_one) in the local analysis at $p$ of the curves attached to a Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_nnnorm_twistParam_eq_one.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Tactic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
namespace WeierstrassCurve
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem nnnorm_twistParam_eq_one (E E' : WeierstrassCurve K)
    (hc₄ : ‖E.c₄‖₊ = 1) (hΔ : ‖E.Δ‖₊ < 1) (hc₄' : ‖E'.c₄‖₊ = 1) (hΔ' : ‖E'.Δ‖₊ < 1) :
    ‖E.c₆ * E'.c₄ / (E'.c₆ * E.c₄)‖₊ = 1 := by sorry
