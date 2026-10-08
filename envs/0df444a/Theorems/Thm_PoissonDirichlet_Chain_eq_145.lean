-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_eq_145
-- name    : PoissonDirichlet.Chain.eq_145
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:59.687612+00:00
-- url     : https://prove2.me/theorems/af9a57ba-0bf3-440a-b623-ee9ca079cdb3
-- title:
--   Display (145), p. 888 — E*_{α,θ}[f(R_1, R_2, …)] = Γ(θ/α + 1)^{−1} E_{α,0}[L^{θ/α} Y_1^{−θ} f(R_1, R_2, …)]
-- statement:
--   Let $0 < \alpha < 1$ and $\theta > -\alpha$. Let $P_{\alpha,0}$ govern $(V_n)$ with the $\mathrm{PD}(\alpha,0)$ law, with local time $L = \lim_n nV_n^\alpha$ (24), ratios $R_n = V_{n+1}/V_n$ and $Y_n = V_n/(V_n + V_{n+1} + \cdots)$; let $P^*_{\alpha,\theta}$ make $R_1, R_2, \dots$ independent with $R_n \sim \mathrm{beta}(\theta+n\alpha,1)$. For every nonnegative product measurable $f$
--   $$E^*_{\alpha,\theta}[f(R_1, R_2, \dots)] = \Gamma(\theta/\alpha+1)^{-1}\,E_{\alpha,0}\big[L^{\theta/\alpha}\,Y_1^{-\theta}\,f(R_1, R_2, \dots)\big],$$
--   and the same formula holds with $f(Y_1, Y_2, \dots)$ in place of $f(R_1, R_2, \dots)$, where under $P^*_{\alpha,\theta}$ the $Y_n$ are given by (125).
--
--   Comparing this with (42) gives the tilt formula (137) of Theorem 38.
--
--   **Formalization Note.** Under $\mathrm{PD}(\alpha,0)$, $\sum_n V_n = 1$ almost surely, so $Y_1 = V_1$; the statement writes $V_1^{-\theta}$. On the left of the second identity $Y_n$ is computed from the ratios by (125); on the right it is computed from $(V_n)$ by (45).
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 888, proof of Theorem 38 (i), (145)

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- (145), p. 888: with `P_{α,0}` governing `(V_n)` with `PD(α, 0)` law, `L` its local time
(24), and `P*_{α,θ}` as in Theorem 38, for every nonnegative measurable `f`
`E*_{α,θ}[f(R_1, R_2, …)] = Γ(θ/α + 1)^{-1} E_{α,0}[L^{θ/α} Y_1^{-θ} f(R_1, R_2, …)]`,
and the same with `f(Y_1, Y_2, …)` in place of `f(R_1, R_2, …)` (by (125)).
`Y_1 = V_1` since `Σ V_n = 1`; the statement writes `V_1`. -/
theorem eq_145 (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω)))
    (μ : Measure (ℕ → ℝ)) (hμ : IsStarLaw α θ μ) :
    (∀ f : (ℕ → ℝ) → ENNReal, Measurable f →
      ∫⁻ r, f r ∂μ =
        ENNReal.ofReal (1 / Real.Gamma (θ / α + 1)) *
          ∫⁻ ω, ENNReal.ofReal (L ω ^ (θ / α) * V ω 0 ^ (-θ)) * f (fun i => PoissonDirichlet.Ratio.ratio (V ω) i) ∂P) ∧
    (∀ f : (ℕ → ℝ) → ENNReal, Measurable f →
      ∫⁻ r, f (YofR r) ∂μ =
        ENNReal.ofReal (1 / Real.Gamma (θ / α + 1)) *
          ∫⁻ ω, ENNReal.ofReal (L ω ^ (θ / α) * V ω 0 ^ (-θ)) * f (Yseq (V ω)) ∂P) := by sorry

end PoissonDirichlet.Chain
