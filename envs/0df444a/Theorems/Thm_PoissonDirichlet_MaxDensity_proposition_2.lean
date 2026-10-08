-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_proposition_2
-- name    : PoissonDirichlet.MaxDensity.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:07.060953+00:00
-- url     : https://prove2.me/theorems/7e154601-1a26-4b57-b54b-2421572f0bb5
-- title:
--   Proposition 2, p. 857 — V_1 > V_2 > ⋯ > 0, ∑V_n = 1 a.s., and stick-breaking is a size-biased permutation of the ranked values
-- statement:
--   Let $0 \le \alpha < 1$ and $\theta > -\alpha$. Let $\tilde Y_1, \tilde Y_2, \dots$ be independent random variables with $\tilde Y_n \sim \mathrm{beta}(1-\alpha, \theta + n\alpha)$, let
--   $$\tilde V_1 = \tilde Y_1, \qquad \tilde V_n = (1-\tilde Y_1)\cdots(1-\tilde Y_{n-1})\tilde Y_n \quad (n \ge 2),$$
--   and let $V_1 \ge V_2 \ge \cdots$ be the ranked values of the $\tilde V_n$. Then almost surely
--   $$V_1 > V_2 > \cdots > 0 \qquad\text{and}\qquad \sum_n V_n = 1,$$
--   and $(\tilde V_n)$ is a size-biased permutation of $(V_n)$.
--
--   This is the bridge between the two descriptions of $\mathrm{PD}(\alpha,\theta)$: the ranked frequencies and the stick-breaking (GEM) order in which sampling discovers them. The paper cites it from McCloskey, Perman–Pitman–Yor and Pitman.
--
--   **Formalization Note.** Indices are 0-based. The $\tilde Y_n$ are taken measurable (they are random variables), which the size-biased permutation property, a statement about conditional expectations, needs.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 857, Proposition 2

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Proposition 2, p. 857 (Pitman–Yor 1997, citing [48, 51, 56]). In the setting of
Definition 1 — independent `Ỹₙ ~ beta(1 - α, θ + nα)` (0-based: `Ytil k` is `Ỹ_{k+1}`),
`Ṽ = PoissonDirichlet.Ratio.stick Ỹ` as in (4), and `V` the PoissonDirichlet.Ratio.ranked values of `Ṽ` — almost surely
`V₁ > V₂ > ⋯ > 0` and `∑ₙ Vₙ = 1`, and `(Ṽₙ)` is a size-biased permutation of `(Vₙ)`. -/
theorem proposition_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P) :
    (∀ᵐ ω ∂P, StrictAnti (PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω)) ∧
        (∀ k, 0 < PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) k) ∧
        HasSum (PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω)) 1) ∧
      IsSizeBiasedPerm P (fun ω => PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω))
        (fun ω => PoissonDirichlet.Ratio.stick fun k => Ytil k ω) := by sorry

end PoissonDirichlet.MaxDensity
