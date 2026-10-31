-- Prove2me | Theorems.Thm_PeriodicEval_static_merton_value
-- name    : PeriodicEval.static_merton_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:10.244624+00:00
-- url     : https://prove2.me/theorems/23b86bb3-f829-4737-951d-b31fef5fa2a7
-- title:
--   Proof of Proposition 4, p.40 — the static Merton value $\sup_{Y\in L_{0,\tau}(1)}E[Y^\alpha]=e^{h\tau}$
-- statement:
--   Under the standing assumptions,
--
--   $$\sup_{Y\in L_{0,\tau}(1)}E[Y^\alpha]=e^{h\tau},\qquad h=r\alpha+\frac{\alpha\theta^2}{2(1-\alpha)},$$
--
--   where $L_{0,\tau}(1)$ is the set of nonnegative $\mathcal F_\tau$-measurable $Y$ with $E[Z_\tau Y\mid\mathcal F_0]\le1$. This is the value of the finite-horizon Merton problem with utility $w^\alpha$, maturity $\tau$ and unit initial wealth. It gives the Lipschitz constant of $\Phi$ in Proposition 4 and the upper bound of Lemma 3.
--
--   Differences from the source:
--   - encoding: sup_{Y ∈ L_{0,τ}(1)} E[Y^α] as a real or extended-real supremum → sSup in EReal; reason: an unbounded set gives ⊤ instead of a junk real value; on bounded sets the value is the paper's
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Proposition 4, p.40

import Mathlib
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PeriodicEval

/-- The static Merton value, SSRN 3971852 (June 20, 2023), proof of Proposition 4, p.40:
`sup_{Y ∈ L_{0,τ}(1)} E[Y^α] = e^{hτ}`, "the value function of a standard finite horizon Merton
problem with utility function u(w) = w^α, maturity τ and unit initial wealth".

**Formalization Note** The supremum is in `EReal`. Each `E[Y^α]` is a genuine expectation
(`Y ≥ 0` and `E[Z_τ Y] ≤ 1` give `E[Y^α] < ∞` by Hölder). -/
theorem static_merton_value (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) :
    sSup {z : EReal | ∃ Y ∈ L p P ℱ B 0 p.τ.toNNReal 1,
        z = ((∫ ω, Y ω ^ p.α ∂P : ℝ) : EReal)} =
      ((Real.exp (p.h * p.τ) : ℝ) : EReal) := by sorry

end PeriodicEval
