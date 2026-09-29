-- Prove2me | Theorems.Thm_TateCurve_symAdd_sum_allParams_unconditional
-- name    : TateCurve.symAdd_sum_allParams_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/932a9970-535b-59f9-b08c-4a346518012c
-- title:
--   Symmetric addition identity for Tate curve X-coordinates, all admissible parameters
-- statement:
--   Let $K$ be a complete, nontrivially normed field of characteristic zero whose norm is ultrametric and which is algebraically closed, and let $q \in K$ satisfy $q \neq 0$ and $\lVert q\rVert < 1$. The assertion is that for all $u, v \in K$ satisfying [`TateCurve.AddParams q u v`](def/TateCurve_XMultStructure.html#L89), i.e. $q \neq 0$, $u \neq 0$, $v \neq 0$ and each of $u$, $v$, $uv$, $uv^{-1}$ is off the lattice in the sense that $q^{n} w \neq 1$ for every $n \in \mathbb{Z}$ (with $w$ the parameter in question), one has
--   $$\bigl(X(uv) + X(uv^{-1})\bigr)\bigl(X(u) - X(v)\bigr)^{2} = 2X(u)X(v)\bigl(X(u)+X(v)\bigr) + X(u)X(v) + 2a_4(q)\bigl(X(u)+X(v)\bigr) + 4a_6(q),$$
--   where $X(w) = \bigl(\sum_{n \in \mathbb{Z}} \mathrm{xfun}(q^{n}w)\bigr) - 2s_1(q)$ is [`TateCurve.pointX q w`](def/TateCurve_PointSeries.html#L179), the right-hand side being [`TateCurve.symSumNum q (pointX q u) (pointX q v)`](def/TateCurve_XMultStructure.html#L20) with $a_4(q)$, $a_6(q)$ the coefficients of the Tate curve attached to $q$.
--
--   This is the symmetric half (the "sum" relation) of the addition law for the $X$-coordinates of the Tate parametrisation, valid for every admissible pair of parameters rather than only in the region where the defining series may be compared term by term. It is the `sum` input to [`TateCurve.symAddHyps_unconditional`](thm.html#TateCurve.symAddHyps_unconditional), which packages the addition-law hypotheses used in the construction of the Tate curve and its Galois module of torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_symAdd_sum_allParams_unconditional.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem TateCurve.symAdd_sum_allParams_unconditional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    ∀ u v : K, TateCurve.AddParams q u v →
      (TateCurve.pointX q (u * v) + TateCurve.pointX q (u * v⁻¹)) * (TateCurve.pointX q u - TateCurve.pointX q v) ^ 2 =
        TateCurve.symSumNum q (TateCurve.pointX q u) (TateCurve.pointX q v) := by sorry
