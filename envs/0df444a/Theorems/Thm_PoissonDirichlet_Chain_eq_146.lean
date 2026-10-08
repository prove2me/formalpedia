-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_eq_146
-- name    : PoissonDirichlet.Chain.eq_146
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:32.220983+00:00
-- url     : https://prove2.me/theorems/dee3f6af-1a49-4d19-8495-7feec0e0d49a
-- title:
--   Display (146), p. 889 — P*_{α,θ}(Y_n ∈ dy) = P*_{α,θ+(n−1)α}(Y_1 ∈ dy)
-- statement:
--   Let $0<\alpha<1$, $\theta>-\alpha$ and $n \ge 1$. Let $P^*_{\alpha,\theta}$ make $R_1, R_2, \dots$ independent with $R_m \sim \mathrm{beta}(\theta+m\alpha,1)$, and let $Y_n = (1 + R_n + R_nR_{n+1} + \cdots)^{-1}$ (125). Then
--   $$P^*_{\alpha,\theta}(Y_n \in dy) = P^*_{\alpha,\theta+(n-1)\alpha}(Y_1 \in dy).$$
--
--   The shift of parameter is what makes the transition density (139) expressible through the single family $r(\alpha, \cdot, \cdot)$ of (140).
--
--   **Formalization Note.** 0-based, $n = k+1$: the law of `YofR r k` under $P^*_{\alpha,\theta}$ equals the law of `YofR r 0` under $P^*_{\alpha,\theta+k\alpha}$, as equality of the measures of preimages of every Borel set.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 889, proof of Theorem 38 (ii), (146)

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- (146), p. 889, with `n = k + 1`: `P*_{α,θ}(Y_n ∈ dy) = P*_{α,θ+(n-1)α}(Y_1 ∈ dy)`. Here
`μ` is `P*_{α,θ}`, `μ'` is `P*_{α,θ+kα}`, and `YofR r k` is `Y_{k+1}`. -/
theorem eq_146 (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (k : ℕ)
    (μ : Measure (ℕ → ℝ)) (hμ : IsStarLaw α θ μ)
    (μ' : Measure (ℕ → ℝ)) (hμ' : IsStarLaw α (θ + (k : ℝ) * α) μ') :
    ∀ s : Set ℝ, MeasurableSet s →
      μ ((fun r => YofR r k) ⁻¹' s) = μ' ((fun r => YofR r 0) ⁻¹' s) := by sorry

end PoissonDirichlet.Chain
