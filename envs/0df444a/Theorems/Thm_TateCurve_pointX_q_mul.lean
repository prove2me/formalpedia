-- Prove2me | Theorems.Thm_TateCurve_pointX_q_mul
-- name    : TateCurve.pointX_q_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/f16b8c9a-e56c-568d-b155-aae9939c4c55
-- title:
--   Invariance of the Tate X-series under u ↦ qu
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $q, u \in K$ with $q \neq 0$. The quantity $\mathrm{pointX}\,q\,u$ is defined as the unconditional sum over all integers $n$ of the terms $\mathrm{xTerm}\,q\,u\,n = \mathrm{xfun}(q^{n}u)$, minus $2\,s_{1}(q)$, where $\mathrm{xfun}$ and $s_{1}$ are the functions of the Tate parametrisation fixed in the project and $q^{n}$ is the integral power. The assertion is the equality $\mathrm{pointX}\,q\,(qu) = \mathrm{pointX}\,q\,u$: replacing $u$ by $qu$ leaves the value unchanged. Note that the sum is taken as a `tsum`, so the statement is an identity of unconditional sums with no summability hypothesis imposed; the subtracted term $2\,s_{1}(q)$ depends only on $q$ and is common to both sides. The hypothesis $q \neq 0$ enters through the identity $q^{n}\cdot q = q^{n+1}$ for integral exponents.
--
--   This is the $q$-periodicity of the $X$-coordinate of the Tate parametrisation; together with the invariance of $\mathrm{pointX}$ under $u \mapsto u^{-1}$ it expresses that $X$ is a function on $K^{\times}/q^{\mathbb{Z}}$ up to the Weierstrass involution. It is used in the construction of points on the Tate curve, in particular in the existence of chord and tangent slopes at non-toric points of the modular curve setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_pointX_q_mul.lean

import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.pointX_q_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) : pointX q (q * u) = pointX q u := by sorry
