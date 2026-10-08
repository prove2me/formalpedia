-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_eq_144
-- name    : PoissonDirichlet.Chain.eq_144
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:52.313087+00:00
-- url     : https://prove2.me/theorems/1541ea04-237a-4707-9741-e3c1a8874e69
-- title:
--   Display (144), p. 888 — E*_{α,θ}[f(R_1,…,R_n)] = Γ(θ/α+n+1)/(Γ(θ/α+1)Γ(n+1)) E_{α,0}[(R_1⋯R_n)^θ f(R_1,…,R_n)]
-- statement:
--   Let $0 < \alpha < 1$ and $\theta > -\alpha$. Let $P_{\alpha,0}$ govern $(V_n)$ with the $\mathrm{PD}(\alpha,0)$ law and $R_n = V_{n+1}/V_n$, and let $P^*_{\alpha,\theta}$ make $R_1, R_2, \dots$ independent with $R_n \sim \mathrm{beta}(\theta+n\alpha, 1)$. Then for every $n \ge 1$ and every nonnegative measurable $f$ on $\mathbb R^n$
--   $$E^*_{\alpha,\theta}[f(R_1,\dots,R_n)] = \frac{\Gamma(\theta/\alpha+n+1)}{\Gamma(\theta/\alpha+1)\Gamma(n+1)}\,E_{\alpha,0}\big[(R_1\cdots R_n)^\theta f(R_1,\dots,R_n)\big].$$
--
--   It is the finite-dimensional form of the change of measure from $P_{\alpha,0}$ to $P^*_{\alpha,\theta}$: both make $R_1,\dots,R_n$ independent beta variables (Proposition 8 under $P_{\alpha,0}$), and the factor is the ratio of the two product densities.
--
--   **Formalization Note.** 0-based, with $n = k+1$. $(R_1\cdots R_n)^\theta$ is a real power of a positive number almost surely.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 888, proof of Theorem 38 (i), (144)

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- (144), p. 888, with `n = k + 1`: if `P_{α,0}` governs `(V_n)` with `PD(α, 0)` law and
`P*_{α,θ}` makes `R_1, R_2, …` independent with `R_n ~ beta(θ + nα, 1)`, then for every
nonnegative measurable `f` of `n` variables
`E*_{α,θ}[f(R_1, …, R_n)] = Γ(θ/α + n + 1) / (Γ(θ/α + 1) Γ(n + 1)) · E_{α,0}[(R_1 ⋯ R_n)^θ
f(R_1, …, R_n)]`. -/
theorem eq_144 (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (μ : Measure (ℕ → ℝ)) (hμ : IsStarLaw α θ μ)
    (k : ℕ) (f : (Fin (k + 1) → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ r, f (fun i => r i) ∂μ =
      ENNReal.ofReal (Real.Gamma (θ / α + ((k : ℝ) + 1) + 1) /
          (Real.Gamma (θ / α + 1) * Real.Gamma (((k : ℝ) + 1) + 1))) *
        ∫⁻ ω, ENNReal.ofReal ((∏ i : Fin (k + 1), PoissonDirichlet.Ratio.ratio (V ω) i) ^ θ) *
          f (fun i => PoissonDirichlet.Ratio.ratio (V ω) i) ∂P := by sorry

end PoissonDirichlet.Chain
