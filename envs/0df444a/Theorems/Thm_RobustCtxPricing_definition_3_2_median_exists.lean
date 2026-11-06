-- Prove2me | Theorems.Thm_RobustCtxPricing_definition_3_2_median_exists
-- name    : RobustCtxPricing.definition_3_2_median_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:53.13221+00:00
-- url     : https://prove2.me/theorems/b174904e-071b-418a-80bf-112f5b9554f4
-- title:
--   Definition 3.2 — the $\epsilon$-window median exists
-- statement:
--   Let $d\ge1$, let $\mu:\mathbb R^d\to\mathbb R$ be nonnegative on $\Theta=\mathcal B_d(0,1)$ and integrable on $\Theta$, let $u\in\mathbb R^d$ and $\epsilon>0$. Then there is $m\in\mathbb R$ with
--   $$
--   \int_\Theta\mu(\theta)\,\mathbb I\{\langle u,\theta\rangle\le m-\epsilon/2\}\,d\theta=\int_\Theta\mu(\theta)\,\mathbb I\{\langle u,\theta\rangle\ge m+\epsilon/2\}\,d\theta .
--   $$
--   So the $\epsilon$-window median of Definition 3.2 exists for every density the algorithm uses, and the exploration step of Algorithm 4 can always be carried out.
--
--   Differences from the source:
--   - generalization: "all the distributions that we work with", derived from continuous densities → every nonnegative function integrable on Θ (no normalization, no continuity), every direction u ∈ ℝ^d and every ϵ > 0; reason: every density of Algorithm 4 is the uniform density times finitely many factors in {1/2, 1, 3/2}, so it is covered
--   - reading: "the ϵ-window median is always well defined" → some m satisfies (3); reason: the solution need not be unique (uniform density, ‖u‖₂ < ϵ/2: every |m| < ϵ/2 − ‖u‖₂ solves (3)), and Algorithm 4 uses any solution
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball; reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); the closed ball contains the open one and differs from it by a null set
--   - encoding: the dimension d ∈ ℕ of ℝ^d → a natural number d with 1 ≤ d; reason: the context dimension of the model; d = 0 has no directions and is not an instance of it
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Definition 3.2 and the remark after Equation (3), p.14

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Density

open MeasureTheory

namespace RobustCtxPricing

/-- **Definition 3.2, well-definedness of the ϵ-window median.** Castiglioni–Stradi, *Decoupling
Corruption and Horizon in Robust Contextual Pricing*, arXiv:2607.11210, §3.1, p.14: after (3),
"since all the distributions that we work with are derived from continuous density functions, they
do not have point masses. Hence, the ϵ-window median is always well defined."

For every `d ≥ 1`, every nonnegative function `μ` integrable on `Θ`, every direction `u ∈ ℝ^d` and
every `ϵ > 0`, some `m ∈ ℝ` satisfies (3).

**Formalization Note.** Stated for every nonnegative integrable `μ` on `Θ` (no normalization, no
continuity), which covers every density of Algorithm 4 (the uniform density multiplied by finitely
many factors in `{1/2, 1, 3/2}` on half-spaces and slabs), and for every `u`, including `u = 0`. -/
theorem definition_3_2_median_exists (d : ℕ) (hd : 1 ≤ d)
    (μ : EuclideanSpace ℝ (Fin d) → ℝ) (hμ : IntegrableOn μ (Theta d))
    (hμ0 : ∀ θ ∈ Theta d, 0 ≤ μ θ) (u : EuclideanSpace ℝ (Fin d)) (ϵ : ℝ) (hϵ : 0 < ϵ) :
    ∃ m : ℝ, IsWindowMedian ϵ μ u m := by sorry

end RobustCtxPricing
