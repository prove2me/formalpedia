-- Prove2me | Theorems.Thm_PoissonDirichlet_Ratio_poisson_ratio_beta
-- name    : PoissonDirichlet.Ratio.poisson_ratio_beta
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:58.329504+00:00
-- url     : https://prove2.me/theorems/b0112b75-0915-4aa5-9ea7-d2069d4feba3
-- title:
--   Poisson arrival ratios are independent beta(n, 1) variables
-- statement:
--   Let $\varepsilon_1,\varepsilon_2,\ldots$ be independent standard exponential variables and $X_n=\varepsilon_1+\cdots+\varepsilon_n$. The consecutive arrival ratios are mutually independent, and for every $n\geq1$,
--
--   $$
--   \frac{X_n}{X_{n+1}}\sim\operatorname{beta}(n,1).
--   $$
--
--   This is the elementary Poisson process fact stated in the proof of Proposition 8. It can be reused for other arrival-time representations.
--
--   **Formalization Note** Lean uses index $k=n-1$, so the first beta parameter is `k+1`. The points of the homogeneous Poisson process are encoded, as in (28), as partial sums of independent standard exponential variables (rate 1; the ratios do not depend on the rate).
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 870, §4.1, proof of Proposition 8, last sentence

import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Ratio

/-- The Poisson-arrival ratio claim in the proof of Proposition 8, p. 870. -/
theorem poisson_ratio_beta {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ)
    (hind : iIndepFun ε P)
    (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P) :
    let X : Ω → ℕ → ℝ := fun ω k =>
      ∑ i ∈ Finset.range (k + 1), ε i ω
    iIndepFun (fun k ω => X ω k / X ω (k + 1)) P ∧
      ∀ k : ℕ, HasLaw (fun ω => X ω k / X ω (k + 1))
        (betaMeasure ((k : ℝ) + 1) 1) P := by sorry

end PoissonDirichlet.Ratio
