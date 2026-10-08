-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_eq_143
-- name    : PoissonDirichlet.Chain.eq_143
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:56.427157+00:00
-- url     : https://prove2.me/theorems/b6d8873d-f13e-417f-99cf-578c66b501a6
-- title:
--   Display (143), p. 888 — L = Y_1^α lim n(R_1⋯R_n)^α, P_{α,θ}-a.s.
-- statement:
--   Let $0 < \alpha < 1$, $\theta > -\alpha$, suppose $(V_n)$ has the $\mathrm{PD}(\alpha,\theta)$ distribution, and let $L = \lim_n nV_n^\alpha$ be the local time (24). With $R_n = V_{n+1}/V_n$ and $Y_1 = V_1/(V_1 + V_2 + \cdots)$,
--   $$L = Y_1^\alpha \lim_{n\to\infty} n(R_1\cdots R_n)^\alpha \qquad (P_{\alpha,\theta}\text{ a.s.}).$$
--
--   The formula expresses the local time through the ratios $R_n$ and $Y_1$, which is what allows the change of measure (144) on the ratios to be passed to the limit in (145).
--
--   **Formalization Note.** 0-based: the statement is that $Y_1^\alpha\,(k+1)(R_1\cdots R_{k+1})^\alpha \to L$ almost surely as $k\to\infty$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 888, proof of Theorem 38 (i), (143)

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- (143), p. 888, 0-based: under `PD(α, θ)` (`0 < α < 1`, `θ > -α`), with `L = lim n V_n^α`
the local time (24), `L = Y_1^α lim_{n → ∞} n (R_1 ⋯ R_n)^α` almost surely. Here
`Yseq (V ω) 0` is `Y_1` and `∏_{i < k+1} PoissonDirichlet.Ratio.ratio (V ω) i` is `R_1 ⋯ R_{k+1}`. -/
theorem eq_143 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V)
    (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => Yseq (V ω) 0 ^ α *
        (((k : ℝ) + 1) * (∏ i ∈ Finset.range (k + 1), PoissonDirichlet.Ratio.ratio (V ω) i) ^ α)) atTop (𝓝 (L ω)) := by sorry

end PoissonDirichlet.Chain
