-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_proposition_34
-- name    : PoissonDirichlet.MaxDensity.proposition_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:29.958581+00:00
-- url     : https://prove2.me/theorems/29984f59-60d2-4c57-9286-405f0177f7c1
-- title:
--   Proposition 34, p. 881 — deleting a sampled frequency V_N and renormalising gives PD(α, θ + α), independent of V_N ~ beta(1 − α, θ + α)
-- statement:
--   Let $0 \le \alpha < 1$, $\theta > -\alpha$, and let $(V_n)$ have the $\mathrm{PD}(\alpha,\theta)$ distribution. Let $N$ be a sample from $(V_n)$, i.e. $P(N = n \mid V_1, V_2, \dots) = V_n$. Let $(V'_n)$ be obtained from $(V_n)$ by deleting $V_N$, and put
--   $$V''_n = \frac{V'_n}{1 - V_N}, \qquad n = 1, 2, \dots.$$
--   Then $(V''_n)$ has the $\mathrm{PD}(\alpha, \theta+\alpha)$ distribution, independently of $V_N$, and
--   $$V_N \sim \mathrm{beta}(1-\alpha,\ \theta+\alpha).$$
--
--   In particular $\mathrm{PD}(0,\theta)$ is invariant under size-biased deletion and renormalisation, and repeated deletion from $\mathrm{PD}(\alpha,0)$ yields $\mathrm{PD}(\alpha,\alpha), \mathrm{PD}(\alpha,2\alpha), \dots$.
--
--   **Formalization Note.** Indices are 0-based. $V$ and $N$ are measurable, as part of the definition of a sample.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 881, Proposition 34

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
import Definitions.Def_PoissonDirichlet_MaxDensity_Sampling
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Proposition 34, p. 881 (Pitman–Yor 1997). Let `N` be a sample (113) from `(Vₙ)` with
`PD(α, θ)` distribution, `0 ≤ α < 1`, `θ > -α`. Let `(V'ₙ)` be obtained from `(Vₙ)` by
deletion of `V_N` and `V''ₙ = V'ₙ / (1 - V_N)`. Then `(V''ₙ)` has `PD(α, θ + α)`
distribution, independently of `V_N`, which has `beta(1 - α, θ + α)` distribution.
(0-based: `N ω = k` is the paper's `N = k + 1`.) -/
theorem proposition_34 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V) (N : Ω → ℕ) (hN : IsSample P V N) :
    PoissonDirichlet.Ratio.HasPD α (θ + α) P (fun ω n => deleteAt (V ω) (N ω) n / (1 - V ω (N ω))) ∧
      IndepFun (fun ω n => deleteAt (V ω) (N ω) n / (1 - V ω (N ω))) (fun ω => V ω (N ω)) P ∧
      HasLaw (fun ω => V ω (N ω)) (betaMeasure (1 - α) (θ + α)) P := by sorry

end PoissonDirichlet.MaxDensity
