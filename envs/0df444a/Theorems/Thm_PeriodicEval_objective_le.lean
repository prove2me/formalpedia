-- Prove2me | Theorems.Thm_PeriodicEval_objective_le
-- name    : PeriodicEval.objective_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:52.460138+00:00
-- url     : https://prove2.me/theorems/6e2bd369-26f0-48c6-9931-fad155a4a583
-- title:
--   Proof of Theorem 1, p.43 — the upper bound $V(x)\le A^*x^\alpha$
-- statement:
--   Under the standing assumptions, let $x>0$ and $A^*$ the fixed point of $\Phi$. For every $X\in\mathcal A_0(x)$,
--
--   $$E\Big[\sum_{i=1}^\infty e^{-\beta T_i}U(X_{T_i}-\gamma X_{T_{i-1}})\Big]\le A^*x^\alpha,$$
--
--   and therefore $V(x)\le A^*x^\alpha$. This is one half of the identity $V(x)=A^*x^\alpha$ of Theorem 1.
--
--   Differences from the source: none.
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Theorem 1, p.43

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- The upper bound, SSRN 3971852 (June 20, 2023), proof of Theorem 1, p.43: for `x > 0`, every
`X ∈ A_0(x)` and `A*` the fixed point of `Φ`,
`E[∑_{i=1}^∞ e^{−βT_i}U(X_{T_i} − γX_{T_{i−1}})] ≤ A*x^α`, and therefore `V(x) ≤ A*x^α`. -/
theorem objective_le (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (x : ℝ) (hx : 0 < x) (A : ℝ) (hA : Φ p P ℱ B A = (A : EReal)) :
    (∀ X ∈ admissible p P ℱ B 0 x, objective p P X ≤ A * x ^ p.α) ∧
    V p P ℱ B x ≤ ((A * x ^ p.α : ℝ) : EReal) := by sorry

end PeriodicEval
