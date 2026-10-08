-- Prove2me | Theorems.Thm_PoissonDirichlet_Ratio_proposition_8
-- name    : PoissonDirichlet.Ratio.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:25.065007+00:00
-- url     : https://prove2.me/theorems/5ef13c9f-6244-4e29-9988-4832f64195e7
-- title:
--   Proposition 8: independent beta laws for ranked PD ratios
-- statement:
--   Suppose $(V_n)$ has $\mathrm{PD}(\alpha,0)$ distribution for $0<\alpha<1$, and put $R_n=V_{n+1}/V_n$. The variables $R_n$ are mutually independent; each has beta$(n\alpha,1)$ distribution, equivalently
--
--   $$
--   \mathbb P(R_n\leq r)=r^{n\alpha}\qquad(0\leq r\leq1).
--   $$
--
--   This identifies the law of every adjacent ranked-frequency ratio and underlies the reconstruction of the whole $\mathrm{PD}(\alpha,0)$ sequence from independent ratios.
--
--   **Formalization Note** Lean's index $k=0$ is the paper's $n=1$; the beta parameter is $(k+1)\alpha$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 861, Proposition 8, (21)–(22)

import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Ratio

/-- Proposition 8, equations (21)–(22): the ratios of adjacent ranked
PD(α,0) frequencies have independent beta laws and the stated CDF. -/
theorem proposition_8 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : HasPD α 0 P V) :
    iIndepFun (fun k ω => ratio (V ω) k) P ∧
      (∀ k : ℕ, HasLaw (fun ω => ratio (V ω) k)
        (betaMeasure (((k : ℝ) + 1) * α) 1) P) ∧
      ∀ k : ℕ, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        P {ω | ratio (V ω) k ≤ r} =
          ENNReal.ofReal (r ^ (((k : ℝ) + 1) * α)) := by sorry

end PoissonDirichlet.Ratio
