-- Prove2me | Theorems.Thm_SherbrookeMetric_PointEstimate_backorders_strictConvexOn
-- name    : SherbrookeMetric.PointEstimate.backorders_strictConvexOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:23.260551+00:00
-- url     : https://prove2.me/theorems/d2975903-1aff-4e64-9019-6bf20b89fc13
-- title:
--   p. 139 — for spare stock $s \ge 1$, $\lambda \mapsto B(s \mid \lambda)$ is strictly convex on $\lambda > 0$
-- statement:
--   Let $B(s \mid \lambda) = \sum_{x=s+1}^{\infty}(x - s)\,e^{-\lambda}\lambda^x/x!$ be the expected backorders at spare stock $s$ under Poisson demand with mean $\lambda$. For every spare stock $s \ge 1$, the function
--   $$\lambda \longmapsto B(s \mid \lambda)$$
--   is strictly convex on the open half-line $(0, \infty)$: for $0 < \lambda_1 \ne \lambda_2$ and $0 < t < 1$,
--   $$B\big(s \mid t\lambda_1 + (1-t)\lambda_2\big) < t\,B(s \mid \lambda_1) + (1-t)\,B(s \mid \lambda_2).$$
--
--   This is the sentence of Sherbrooke (1968), p. 139, "for any positive $\lambda$ and spare stock of one or more, the number of backorders is a strictly convex function of $\lambda$". It is the property that turns uncertainty about the mean demand into a systematic underestimate when a point estimate is used.
--
--   **Formalization Note** Stated with Mathlib's `StrictConvexOn ℝ (Set.Ioi 0)`, matching the paper's "for any positive $\lambda$".
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 139, Demand Prediction (sentence after Eq. (10))

import Mathlib
import Definitions.Def_SherbrookeMetric_PointEstimate_backorders

namespace SherbrookeMetric.PointEstimate

/-- Sherbrooke (1968), p. 139: for spare stock `s ≥ 1`, Poisson expected backorders
`λ ↦ B(s | λ)` are strictly convex on the positive reals. -/
theorem backorders_strictConvexOn (s : ℕ) (hs : 1 ≤ s) :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (backorders s) := by sorry

end SherbrookeMetric.PointEstimate
