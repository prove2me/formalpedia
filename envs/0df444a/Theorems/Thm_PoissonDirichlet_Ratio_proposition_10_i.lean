-- Prove2me | Theorems.Thm_PoissonDirichlet_Ratio_proposition_10_i
-- name    : PoissonDirichlet.Ratio.proposition_10_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:07.825987+00:00
-- url     : https://prove2.me/theorems/b0ad7a02-d929-4f99-a88b-6fe4db2233a0
-- title:
--   Proposition 10 (i): existence of the local time in every pth mean
-- statement:
--   Let $(V_n)$ have $\mathrm{PD}(\alpha,0)$ law for $0<\alpha<1$. There is a random variable $L$ such that
--
--   $$
--   nV_n^\alpha\longrightarrow L
--   $$
--
--   almost surely and in $L^p$ for every real $p\geq1$. This local time is the scale used to turn the ranked frequencies into Poisson arrival times in Proposition 10 (iii).
--
--   **Formalization Note** Lean indexes $V_n$ as `V ω (n-1)`; `eLpNorm` expresses the $L^p$ norm of the error and must tend to zero.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 862, Proposition 10 (i), (24)

import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Ratio

/-- Proposition 10 (i), equation (24): the local time exists almost surely
and in every p-th mean for p at least one. -/
theorem proposition_10_i {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : HasPD α 0 P V) :
    ∃ L : Ω → ℝ,
      (∀ᵐ ω ∂P, Tendsto
        (fun k : ℕ => ((k : ℝ) + 1) * (V ω k) ^ α)
        atTop (𝓝 (L ω))) ∧
      ∀ p : ℝ, 1 ≤ p → Tendsto
        (fun k : ℕ => eLpNorm
          (fun ω => ((k : ℝ) + 1) * (V ω k) ^ α - L ω)
          (ENNReal.ofReal p) P)
        atTop (𝓝 0) := by sorry

end PoissonDirichlet.Ratio
