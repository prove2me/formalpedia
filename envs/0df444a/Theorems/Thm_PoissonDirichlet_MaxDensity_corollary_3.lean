-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_corollary_3
-- name    : PoissonDirichlet.MaxDensity.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:05.22126+00:00
-- url     : https://prove2.me/theorems/94ae0e78-5c2d-45a7-a728-b3c66fcc7c42
-- title:
--   Corollary 3, p. 858 — a size-biased pick from PD(α, θ) has the beta(1 − α, θ + α) law
-- statement:
--   Let $0 \le \alpha < 1$ and $\theta > -\alpha$, and let $(V_n)$ be a random sequence with the $\mathrm{PD}(\alpha,\theta)$ distribution. If $\tilde V_1$ is a size-biased pick from $(V_n)$, that is $P(\tilde V_1 = V_n \mid V_1, V_2, \dots) = V_n$ for every $n$, then
--   $$\tilde V_1 \sim \mathrm{beta}(1-\alpha,\ \theta+\alpha).$$
--
--   The statement is about every size-biased pick from every sequence with this law, not only about the stick-breaking construction (where $\tilde V_1 = \tilde Y_1$ has this law by definition). It identifies the "structural distribution" of $\mathrm{PD}(\alpha,\theta)$ and is the source of formula (6).
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 858, Corollary 3

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Corollary 3, p. 858 (Pitman–Yor 1997, citing [48, 17, 51, 56]). For `0 ≤ α < 1` and
`θ > -α`, if `W` is a size-biased pick from a sequence `(Vₙ)` with `PD(α, θ)`
distribution, then `W` has the `beta(1 - α, θ + α)` distribution. -/
theorem corollary_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V) (W : Ω → ℝ) (hW : IsSizeBiasedPick P V W) :
    HasLaw W (betaMeasure (1 - α) (θ + α)) P := by sorry

end PoissonDirichlet.MaxDensity
