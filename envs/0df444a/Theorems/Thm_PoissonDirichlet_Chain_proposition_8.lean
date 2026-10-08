-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_proposition_8
-- name    : PoissonDirichlet.Chain.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:55.887009+00:00
-- url     : https://prove2.me/theorems/92fd3c10-30f9-4da6-9569-3ef7fbefa4da
-- title:
--   Proposition 8, p. 861 — under PD(α, 0) the ratios R_n = V_{n+1}/V_n are independent with beta(nα, 1) laws
-- statement:
--   Let $0 < \alpha < 1$ and suppose $(V_n)$ has the $\mathrm{PD}(\alpha, 0)$ distribution. Let $R_n = V_{n+1}/V_n$ (21). Then the $R_n$ are mutually independent and $R_n$ has the $\mathrm{beta}(n\alpha, 1)$ distribution, that is,
--   $$P(R_n \le r) = r^{n\alpha} \qquad (0 \le r \le 1).\qquad (22)$$
--
--   In the language of Theorem 38, $P_{\alpha,0} = P^*_{\alpha,0}$ (Remark 42); the change of measure (144) from $P_{\alpha,0}$ to $P^*_{\alpha,\theta}$ starts from this product structure.
--
--   **Formalization Note.** 0-based: `ratio (V ω) k` is $R_{k+1}$, with law $\mathrm{beta}((k+1)\alpha, 1)$. Restated from mission 1 of this series because drafts cannot import drafts.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 861, Proposition 8, (21), (22)

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- Proposition 8, p. 861, (21)–(22), 0-based: if `(V_n)` has `PD(α, 0)` law for some
`0 < α < 1`, the ratios `R_n = V_{n+1}/V_n` are mutually independent and `R_n` has law
`beta(nα, 1)`, i.e. `P(R_n ≤ r) = r^{nα}` for `0 ≤ r ≤ 1`. Here `ratio (V ω) k` is `R_{k+1}`. -/
theorem proposition_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) :
    iIndepFun (fun k ω => PoissonDirichlet.Ratio.ratio (V ω) k) P ∧
      (∀ k : ℕ, HasLaw (fun ω => PoissonDirichlet.Ratio.ratio (V ω) k) (betaMeasure (((k : ℝ) + 1) * α) 1) P) ∧
      ∀ k : ℕ, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        P {ω | PoissonDirichlet.Ratio.ratio (V ω) k ≤ r} = ENNReal.ofReal (r ^ (((k : ℝ) + 1) * α)) := by sorry

end PoissonDirichlet.Chain
