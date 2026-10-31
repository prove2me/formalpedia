-- Prove2me | Theorems.Thm_PeriodicEval_not_case_4
-- name    : PeriodicEval.not_case_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:57.16727+00:00
-- url     : https://prove2.me/theorems/a1e3926a-61b1-478d-a1f6-9c860a6c12fa
-- title:
--   Proof of Theorem 1, p.44 — Case 4 of Proposition 3 cannot occur at the fixed point
-- statement:
--   Under the standing assumptions, the fixed point $A^*$ of $\Phi$ never satisfies both
--
--   $$-(k^{1/(1-\alpha)}+1)^{1-\alpha}<A^*<-1\qquad\text{and}\qquad|A^*|^{-1/(1-\alpha)}\le1-\gamma e^{-r\tau}.$$
--
--   So at $a=A^*$ the optimizer of the auxiliary problem has the form of Cases 1, 2a, 2b or 3 of Proposition 3, which is what the support table of Theorem 1 lists.
--
--   Differences from the source: none.
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Theorem 1, p.44

import Mathlib
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PeriodicEval

/-- Case 4 of Proposition 3 cannot occur at the fixed point, SSRN 3971852 (June 20, 2023),
proof of Theorem 1, p.44: "it is impossible to observe `−(k^{1/(1−α)} + 1)^{1−α} < A* < −1` and
`|A*|^{−1/(1−α)} ≤ 1 − γe^{−rτ}`".

**Formalization Note** `A*` is any real `A` with `Φ(A) = A`. -/
theorem not_case_4 (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (A : ℝ) (hA : Φ p P ℱ B A = (A : EReal)) :
    ¬(-p.κ < A ∧ A < -1 ∧
      |A| ^ (-1 / (1 - p.α)) ≤ 1 - p.γ * Real.exp (-(p.r * p.τ))) := by sorry

end PeriodicEval
