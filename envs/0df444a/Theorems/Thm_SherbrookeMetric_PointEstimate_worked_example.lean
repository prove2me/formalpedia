-- Prove2me | Theorems.Thm_SherbrookeMetric_PointEstimate_worked_example
-- name    : SherbrookeMetric.PointEstimate.worked_example
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:27.741054+00:00
-- url     : https://prove2.me/theorems/4dbb3ff4-2eb9-471c-8e9c-5d26826cdccb
-- title:
--   p. 138 — worked example: $B(2 \mid 1) \approx 0.1036$ and $B^*(2) \approx 0.1486$ (printed 0.1485)
-- statement:
--   Let $B(s \mid \lambda) = \sum_{x=s+1}^{\infty}(x - s)\,e^{-\lambda}\lambda^x/x!$ be the expected backorders at spare stock $s$ under Poisson demand with mean $\lambda$. Take spare stock $s = 2$.
--
--   1. With the point estimate $\lambda = 1$ of mean demand,
--   $$B(2 \mid 1) = 3e^{-1} - 1, \qquad |B(2 \mid 1) - 0.1036| < 0.00005.$$
--   2. If instead the mean demand is $0.5$ or $1.5$ with probability $0.5$ each (so its mean is still $1$), the expected backorders
--   $$B^*(2) = 0.5\,B(2 \mid 0.5) + 0.5\,B(2 \mid 1.5)$$
--   satisfy $|B^*(2) - 0.1486| < 0.00005$.
--
--   This is the numerical example of Sherbrooke (1968), p. 138, which illustrates that the point estimate understates expected backorders ($0.1036 < 0.1486$).
--
--   **Formalization Note** The paper prints $B^*(2) = 0.1485$. The exact value is $B^*(2) = \tfrac12\big(2.5\,e^{-0.5} + 3.5\,e^{-1.5} - 2\big) = 0.148641\ldots$, which rounds (and truncates) to $0.1486$; the statement uses the corrected four-digit value. The paper's sums start at $x = 2$; the $x = 2$ term is zero, so they agree with eq. (2)'s $x = s + 1 = 3$.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 138, Demand Prediction (worked example)

import Mathlib
import Definitions.Def_SherbrookeMetric_PointEstimate_backorders

namespace SherbrookeMetric.PointEstimate

/-- Sherbrooke (1968), p. 138, the worked example: `B(2 | 1) = 3e^{-1} - 1 ≈ 0.1036`, and the
backorders under the two-point prior `{0.5, 1.5}` with weights `0.5, 0.5` are
`B*(2) = 0.5 B(2 | 0.5) + 0.5 B(2 | 1.5) ≈ 0.1486` (printed `0.1485`, a rounding slip). -/
theorem worked_example :
    backorders 2 1 = 3 * Real.exp (-1) - 1 ∧
    |backorders 2 1 - 0.1036| < 0.00005 ∧
    |(0.5 * backorders 2 0.5 + 0.5 * backorders 2 1.5) - 0.1486| < 0.00005 := by sorry

end SherbrookeMetric.PointEstimate
