-- Prove2me | Theorems.Thm_TateCurve_diffHyp_unconditional
-- name    : TateCurve.diffHyp_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/e8fbdd0f-1b12-5037-a9fc-aa2853ec0a56
-- title:
--   Unconditional difference identity X(uv)-X(uv⁻¹) for the Tate curve
-- statement:
--   Let $K$ be a nontrivially normed field which is complete, ultrametric, of characteristic zero and algebraically closed, and let $q \in K$ satisfy $q \neq 0$ and $\|q\| < 1$. The conclusion is the predicate [`TateCurve.DiffHyp q`](def/TateCurve_KeystoneVocab.html#L52), which asserts: for all $u, v \in K$ such that `AddParams q u v` holds — that is, $q \neq 0$, $u \neq 0$, $v \neq 0$, and each of $u$, $v$, $uv$ and $uv^{-1}$ satisfies the predicate `OffLattice` with respect to $q$ — one has
--   $$\bigl(X(uv) - X(uv^{-1})\bigr)\bigl(X(u) - X(v)\bigr)^{2} = -\bigl(2Y(u) + X(u)\bigr)\bigl(2Y(v) + X(v)\bigr),$$
--   where $X(w) = \mathrm{pointX}\ q\ w$ is the sum of the $\mathbb{Z}$-indexed family `xTerm q w n` minus $2 s_1(q)$, and $Y(w) = \mathrm{pointY}\ q\ w$ is the sum of the family `yTerm q w n` plus $s_1(q)$. Thus the identity is asserted for every admissible pair $(u,v)$, with no restriction to a region of convergence in $u$ and $v$.
--
--   This is the antisymmetric companion of the symmetric addition identity for the Tate parametrisation: in classical notation it is the formula for $x(P+Q) - x(P-Q)$ on the Tate curve, the right-hand side being the product of the two-division values $2Y + X$ at $u$ and at $v$. It is obtained from the regional symmetric identity [`TateCurve.symAdd_sum_regional`](thm.html#TateCurve.symAdd_sum_regional) together with the availability of a square root of $q$ in the algebraically closed field $K$, and it feeds [`TateCurve.symAddHyps_unconditional`](thm.html#TateCurve.symAddHyps_unconditional) and [`TateCurve.symAdd_sum_allParams_unconditional`](thm.html#TateCurve.symAdd_sum_allParams_unconditional), which package the addition law for the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_diffHyp_unconditional.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem TateCurve.diffHyp_unconditional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    TateCurve.DiffHyp q := by sorry
