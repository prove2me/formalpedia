-- Prove2me | Theorems.Thm_TateCurve_pointY_q_mul
-- name    : TateCurve.pointY_q_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/52042651-f841-5980-9d4e-dda4f97de148
-- title:
--   Invariance of the Tate Y-series under u ↦ qu
-- statement:
--   Let $K$ be a nontrivially normed field whose distance is ultrametric and which is complete, and let $q, u \in K$ with $q \neq 0$. For such data the series construction `pointY` assigns to a pair $(q,u)$ the element $\bigl(\sum_{n \in \mathbb{Z}} \mathrm{yfun}(q^{n} u)\bigr) + s_1(q)$ of $K$, where the sum is the unconditional `tsum` over $n \in \mathbb{Z}$ of the terms $\mathrm{yTerm}(q,u,n) = \mathrm{yfun}(q^{n} u)$ built from the function `yfun`, and $s_1(q)$ is the correction term `s₁` depending on $q$ alone. The theorem asserts the equality $\mathrm{pointY}(q, qu) = \mathrm{pointY}(q, u)$, that is, the $Y$-coordinate series of the Tate parametrisation is unchanged when the parameter $u$ is replaced by $qu$. Note that no convergence hypothesis on the series is imposed: the assertion is an identity between the values of `tsum`, which in Lean are defined unconditionally (and equal $0$ when the family is not summable), plus the common summand $s_1(q)$.
--
--   This is the periodicity of the $Y$-coordinate of the Tate parametrisation with respect to the multiplicative lattice $q^{\mathbb{Z}}$, the companion of the corresponding statement for the $X$-coordinate; classically it is the step showing that $u \mapsto (X(u),Y(u))$ factors through $K^{\times}/q^{\mathbb{Z}}$. It is exported by several of the `TateCurve` export bundles used downstream in the treatment of the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_pointY_q_mul.lean

import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.pointY_q_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) : pointY q (q * u) = pointY q u := by sorry
