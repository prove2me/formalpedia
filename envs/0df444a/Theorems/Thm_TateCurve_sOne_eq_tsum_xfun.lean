-- Prove2me | Theorems.Thm_TateCurve_sOne_eq_tsum_xfun
-- name    : TateCurve.sOne_eq_tsum_xfun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/c09d0317-1696-5585-8969-6e00e5daa036
-- title:
--   s₁(q) as the sum of qⁿ/(1-qⁿ)²
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $q \in K$ satisfy $q \neq 0$ and $\lVert q\rVert < 1$ (the inequality being stated for the non-negative-real-valued norm $\lVert\cdot\rVert_+$). The assertion is the identity
--   $$s_1(q) \;=\; \sum_{n = 0}^{\infty} \mathrm{xfun}\bigl(q^{\,n+1}\bigr) \;=\; \sum_{n \ge 1} \frac{q^{n}}{(1 - q^{n})^{2}},$$
--   where `xfun` is the function $w \mapsto w/(1-w)^2$ on $K$, the sum is the unconditional sum (`tsum`) of the indicated family indexed by $n \in \mathbb{N}$, and $s_1(q)$ denotes the quantity `s₁ q` attached to the parameter $q$, namely the first of the two normalising constants occurring in the Tate parametrisation. Thus the right-hand side is shown to converge to $s_1(q)$ for every such $q$; both hypotheses $q \neq 0$ and $\lVert q\rVert_+ < 1$ are used.
--
--   This is the Eisenstein-series identity $\sum_{n\ge1} n q^n/(1-q^n) = \sum_{n\ge1} q^n/(1-q^n)^2$ (both sides being $\sum_{k\ge1}\sigma_1(k)q^k$), specialised to the normalising constant $s_1(q)$ of the Tate curve over a complete non-archimedean field. It is used in [`TateCurve.pointX_normalForm`](thm.html#TateCurve.pointX_normalForm) and [`TateCurve.pointY_normalForm`](thm.html#TateCurve.pointY_normalForm), where the constant $-2s_1(q)$ has to be recognised inside the point series of the Tate parametrisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_sOne_eq_tsum_xfun.lean

import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.sOne_eq_tsum_xfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : s₁ q = ∑' n : ℕ, xfun (q ^ (n + 1)) := by sorry
