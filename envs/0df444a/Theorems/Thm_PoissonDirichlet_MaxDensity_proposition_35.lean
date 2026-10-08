-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_proposition_35
-- name    : PoissonDirichlet.MaxDensity.proposition_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:39.309509+00:00
-- url     : https://prove2.me/theorems/9b16b968-604a-4c03-8285-f8ff280c337b
-- title:
--   Proposition 35, p. 881 — inserting an independent beta(1 − α, θ + α) variable X into (1 − X)·PD(α, α + θ) gives PD(α, θ), with X = V_N
-- statement:
--   Fix $0 \le \alpha < 1$ and $\theta > -\alpha$. Let $(V''_n)$ have the $\mathrm{PD}(\alpha,\alpha+\theta)$ distribution and, independently of it, let $X \sim \mathrm{beta}(1-\alpha, \theta+\alpha)$. Let $(V_n)$ be obtained by inserting $X$ into the sequence $((1-X)V''_n,\ n = 1, 2, \dots)$. Then
--   $$(V_n) \sim \mathrm{PD}(\alpha,\theta),$$
--   and $X = V_N$, where the insertion position $N$ is a sample from $(V_n)$: $P(N = n \mid V_1, V_2, \dots) = V_n$.
--
--   This is the converse of Proposition 34 and gives a recursive construction of $\mathrm{PD}(\alpha,\theta)$ from $\mathrm{PD}(\alpha,\alpha+\theta)$.
--
--   **Formalization Note.** Indices are 0-based. Insertion uses the index $n-1$ for the shifted tail; the page prints $n+1$ (see the definition `insertAt`). The identity $X = V_N$ holds by the definition of insertion and is stated for completeness. $V''$ and $X$ are taken measurable (random variables), which the conditional-probability statement about $N$ needs.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 881, Proposition 35 and §6.1 (insertion)

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
import Definitions.Def_PoissonDirichlet_MaxDensity_Sampling
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Proposition 35, p. 881 (Pitman–Yor 1997). Fix `0 ≤ α < 1`, `θ > -α`. Let `(V''ₙ)` have
`PD(α, α + θ)` distribution and, independent of it, let `X` have `beta(1 - α, θ + α)`
distribution. Let `(Vₙ)` be obtained by insertion of `X` into `((1 - X) V''ₙ)`. Then `(Vₙ)`
has `PD(α, θ)` distribution and `X = V_N`, where the insertion index `N` is a sample from
`(Vₙ)`. (0-based indices; insertion with the corrected index `n - 1`, see `insertAt`.) -/
theorem proposition_35 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (V'' : Ω → ℕ → ℝ) (hV''m : Measurable V'') (hV'' : PoissonDirichlet.Ratio.HasPD α (α + θ) P V'')
    (X : Ω → ℝ) (hXm : Measurable X) (hX : HasLaw X (betaMeasure (1 - α) (θ + α)) P)
    (hind : IndepFun V'' X P) :
    PoissonDirichlet.Ratio.HasPD α θ P (fun ω => insertAt (fun n => (1 - X ω) * V'' ω n) (X ω)) ∧
      IsSample P (fun ω => insertAt (fun n => (1 - X ω) * V'' ω n) (X ω))
        (fun ω => insertIndex (fun n => (1 - X ω) * V'' ω n) (X ω)) ∧
      ∀ ω, insertAt (fun n => (1 - X ω) * V'' ω n) (X ω)
          (insertIndex (fun n => (1 - X ω) * V'' ω n) (X ω)) = X ω := by sorry

end PoissonDirichlet.MaxDensity
