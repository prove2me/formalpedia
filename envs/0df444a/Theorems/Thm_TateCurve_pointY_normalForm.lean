-- Prove2me | Theorems.Thm_TateCurve_pointY_normalForm
-- name    : TateCurve.pointY_normalForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/b7bce871-09d5-5090-bddc-e9a1e9e9ddb0
-- title:
--   Normal form of the Tate Y-coordinate
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $q, u \in K$ satisfy $q \neq 0$, $\|q\|_{+} < 1$, $u \neq 0$, and $q^n u \neq 1$ for every integer $n$ (so that none of the factors $1 - q^n u$ vanishes). Write $\mathrm{xfun}(w) = w/(1-w)^2$ and $\mathrm{yfun}(w) = w^2/(1-w)^3$, and let `pointY` $q\,u$ be the sum of the doubly infinite series $\sum_{n \in \mathbb{Z}} \mathrm{yfun}(q^n u)$ and the quantity $s_1(q)$. The theorem asserts the identity
--   $$\mathrm{pointY}\, q\,u = \frac{u^2}{(1-u)^3} + \sum_{n=0}^{\infty}\left( \mathrm{yfun}(q^{n+1}u) - \mathrm{yfun}(q^{n+1}u^{-1}) - \mathrm{xfun}(q^{n+1}u^{-1}) + \mathrm{xfun}(q^{n+1}) \right),$$
--   the right-hand side being an unconditional sum over the natural numbers. Thus the two-sided sum over $\mathbb{Z}$ together with $s_1(q)$ is rewritten as the term at $n = 0$ plus a one-sided series in the positive powers of $q$, the negative-index terms being folded in through $u^{-1}$ and the $\mathrm{xfun}$ corrections.
--
--   This is the standard closed form for the $Y$-coordinate of the Tate parametrisation $u \mapsto (X(u,q), Y(u,q))$ of the Tate curve, as in Silverman's Theorem V.3.1, and the companion of the corresponding normal form for the $X$-coordinate. The identification of $s_1(q)$ with $\sum_{n \ge 1} \mathrm{xfun}(q^{n})$ is supplied by [`TateCurve.sOne_eq_tsum_xfun`](thm.html#TateCurve.sOne_eq_tsum_xfun); the result feeds into [`TateCurve.pointY_qExpansion`](thm.html#TateCurve.pointY_qExpansion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_pointY_normalForm.lean

import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.pointY_normalForm {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointY q u = yfun u + ∑' n : ℕ, (yfun (q ^ (n + 1) * u) - yfun (q ^ (n + 1) * u⁻¹) - xfun (q ^ (n + 1) * u⁻¹) + xfun (q ^ (n + 1))) := by sorry
