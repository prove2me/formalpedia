-- Prove2me | Theorems.Thm_PoissonDirichlet_Wendel_proposition_8
-- name    : PoissonDirichlet.Wendel.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:55.154972+00:00
-- url     : https://prove2.me/theorems/a2c2f953-d6d6-4019-8e8f-eeab74c17633
-- title:
--   Proposition 8, p. 861 — under PD(α, 0) the ratios R_n = V_{n+1}/V_n are independent, R_n ~ beta(nα, 1)
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ distribution. Let $R_n=V_{n+1}/V_n$. Then the $R_n$ are mutually independent and $R_n$ has the beta$(n\alpha,1)$ distribution, that is,
--   $$P(R_n\le r)=r^{n\alpha}\qquad(0\le r\le1).$$
--
--   In the proof of Proposition 11, independence of the $R_n$ gives part (iii): $A_{n-1}$ is a function of $R_1,\dots,R_{n-1}$ and $\Sigma_n$ of $R_n,R_{n+1},\dots$.
--
--   **Formalization Note** 0-based: `ratio (V ω) k` is $R_{k+1}$, with law beta$((k+1)\alpha,1)$. The distribution function (22) is stated together with the law.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 861, Proposition 8, (21), (22)

import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- Proposition 8, p. 861: for `V` with law PD(α, 0), 0 < α < 1, the ratios
`R_n = V_{n+1} / V_n` are mutually independent, `R_n` has law beta(nα, 1), that is
(22) `P(R_n ≤ r) = r^{nα}` for 0 ≤ r ≤ 1. 0-based: `ratio (V ω) k` is `R_{k+1}`. -/
theorem proposition_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) :
    iIndepFun (fun k ω => PoissonDirichlet.Ratio.ratio (V ω) k) P ∧
    (∀ k : ℕ, HasLaw (fun ω => PoissonDirichlet.Ratio.ratio (V ω) k) (betaMeasure (((k : ℝ) + 1) * α) 1) P) ∧
    (∀ k : ℕ, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      P {ω | PoissonDirichlet.Ratio.ratio (V ω) k ≤ r} = ENNReal.ofReal (r ^ (((k : ℝ) + 1) * α))) := by sorry

end PoissonDirichlet.Wendel
