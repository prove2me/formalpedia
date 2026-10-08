-- Prove2me | Theorems.Thm_TalagrandConc_TSP_isolation_weights
-- name    : TalagrandConc.TSP.isolation_weights
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:19.523196+00:00
-- url     : https://prove2.me/theorems/9c7cac00-d22d-4304-8a98-8a0cc69c2214
-- title:
--   Proposition 11.2.3 — squared isolation weights have bounded sum
-- statement:
--   There is a universal constant $K>0$ such that, for $N\ge1$ independent uniform points $X_1,\ldots,X_N$ of the unit square and $1\le t\le\sqrt N/K$, the isolation weight $\alpha$ defined on p. 176 satisfies
--   $$P\left(\sum_{i=1}^N\alpha(X_i)^2\le K\right)\ge1-Ke^{-t^2}.$$
--
--   The result bounds the combined weight of the sample points even though individual points can be isolated at different dyadic scales.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 176, Proposition 11.2.3, Eq. (11.2.2)

import Mathlib
import Definitions.Def_TalagrandConc_TSP_Basic

namespace TalagrandConc.TSP

open MeasureTheory

/-- Talagrand (1995), Proposition 11.2.3, p. 176. -/
theorem isolation_weights :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (t : ℝ), 0 < N → 1 ≤ t →
      t ≤ Real.sqrt N / K →
      ENNReal.ofReal (1 - K * Real.exp (-t ^ 2)) ≤
        sampleLaw N {x | ∑ i : Fin N, (alpha N t (sampleSet x) (x i)) ^ 2 ≤ K} := by sorry

end TalagrandConc.TSP
