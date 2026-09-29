-- Prove2me | Theorems.Thm_TateCurve_symAdd_sum_regional
-- name    : TateCurve.symAdd_sum_regional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/df9045da-acc7-5265-a743-94cd2cf9f9fb
-- title:
--   Symmetric addition identity for the Tate curve x-series
-- statement:
--   Let $K$ be a nontrivially normed field that is complete, with ultrametric distance, and of characteristic $0$, and let $q \in K$ satisfy $q \neq 0$ and $\|q\| < 1$. The assertion is that for all $u', v' \in K$ lying in the expansion region for $q$ — that is, such that [`TateCurve.ExpansionRegion q u' v'`](def/TateCurve_KeystoneVocab.html#L73) holds, which packages the addition parameters ($q \neq 0$, $u' \neq 0$, $v' \neq 0$, and the predicate `OffLattice q` for each of $u'$, $v'$, $u'v'$ and $u'v'^{-1}$) together with $\|q\| < 1$ and the eight norm bounds $\|q\| < \|w\|$ and $\|q\|\,\|w\| < 1$ for $w = u', v', u'v', u'v'^{-1}$ — one has
--   $$\bigl(X(u'v') + X(u'v'^{-1})\bigr)\bigl(X(u') - X(v')\bigr)^2 = 2x_1x_2(x_1+x_2) + x_1x_2 + 2a_4(q)(x_1+x_2) + 4a_6(q),$$
--   with $x_1 = X(u')$, $x_2 = X(v')$, where $X(w) = \bigl(\sum_{n \in \mathbb{Z}}' \mathrm{xfun}(q^n w)\bigr) - 2s_1(q)$ is [`TateCurve.pointX q w`](def/TateCurve_PointSeries.html#L179) and the right-hand side is [`TateCurve.symSumNum q x₁ x₂`](def/TateCurve_XMultStructure.html#L20). The hypotheses $q \neq 0$ and $\|q\| < 1$ are stated separately, although they are also implied by the expansion-region hypothesis.
--
--   This is the symmetric half of the addition law for the Tate parametrisation: the numerator identity expressing $x(P+Q) + x(P-Q)$ in terms of $x(P)$ and $x(Q)$ for the explicit $q$-expansion series, valid on the region where the relevant series converge and no argument lies on the $q$-lattice. It serves as input to [`TateCurve.diffHyp_unconditional`](thm.html#TateCurve.diffHyp_unconditional) and to [`TateCurve.symAdd_sum_allParams_unconditional`](thm.html#TateCurve.symAdd_sum_allParams_unconditional), which remove the norm restrictions and assemble the group-law statement for the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_symAdd_sum_regional.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem TateCurve.symAdd_sum_regional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] {q : K} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ∀ u' v' : K, TateCurve.ExpansionRegion q u' v' →
      (TateCurve.pointX q (u' * v') + TateCurve.pointX q (u' * v'⁻¹)) * (TateCurve.pointX q u' - TateCurve.pointX q v') ^ 2 =
        TateCurve.symSumNum q (TateCurve.pointX q u') (TateCurve.pointX q v') := by sorry
