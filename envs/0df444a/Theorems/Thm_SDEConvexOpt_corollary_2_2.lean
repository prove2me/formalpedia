-- Prove2me | Theorems.Thm_SDEConvexOpt_corollary_2_2
-- name    : SDEConvexOpt.corollary_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:51.107984+00:00
-- url     : https://prove2.me/theorems/bbc750d1-6bf8-4893-b837-4c0a06a4a65e
-- title:
--   Corollary 2.2 — $\|\nabla f(x)\|^2\le 2L\,(f(x)-\min f)$ for $f\in C^{1,1}_L$ with a minimizer
-- statement:
--   Let $L\ge0$ and let $f\in C^{1,1}_L(\mathbb R^d)$, i.e. $f$ is continuously differentiable and $\nabla f$ is $L$-Lipschitz continuous, and assume $\operatorname{argmin} f\neq\emptyset$. Then
--   $$
--   \|\nabla f(x)\|^2\le 2L\,\big(f(x)-\min f\big)\qquad\text{for all } x\in\mathbb R^d .
--   $$
--   No convexity is assumed. In the proof of Theorem 3.1(iii) this bound turns the integrability of $f(X(t))-\min f$ into that of $\|\nabla f(X(t))\|^2$.
--
--   Differences from the source:
--   - encoding: $\min f$; $C^{1,1}_L(\mathbb R^d)$ with $L\ge0$ → `⨅ y, f y`; `ContDiff ℝ 1 f`, `LipschitzWith L (gradient f)` with `L : ℝ≥0`, on `SDEState d`; reason: the infimum is the minimum since $\operatorname{argmin} f\neq\emptyset$; the class of p.6
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, Corollary 2.2, p.6

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SDEConvexOpt_argminSet

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace SDEConvexOpt

open EthierKurtz

/-- Corollary 2.2 of Maulen S., Fadili, Attouch, arXiv:2207.02750v1, p.6: let
`f ∈ C^{1,1}_L(ℝ^d)` such that `argmin f ≠ ∅`; then `‖∇f(x)‖² ≤ 2L(f(x) − min f)` for all
`x ∈ ℝ^d`.

**Formalization Note** `C^{1,1}_L(ℝ^d)` (p.6, `L ≥ 0`) is `ContDiff ℝ 1 f` with
`LipschitzWith L (gradient f)`, `L : ℝ≥0`; no convexity is assumed, as on the page. `min f` is
`⨅ y, f y`, the minimum value since `argmin f ≠ ∅`. -/
theorem corollary_2_2 {d : ℕ} (f : SDEState d → ℝ) (L : ℝ≥0) (hf : ContDiff ℝ 1 f)
    (hL : LipschitzWith L (gradient f)) (hS : (argminSet f).Nonempty) (x : SDEState d) :
    ‖gradient f x‖ ^ 2 ≤ 2 * (L : ℝ) * (f x - ⨅ y, f y) := by sorry

end SDEConvexOpt
