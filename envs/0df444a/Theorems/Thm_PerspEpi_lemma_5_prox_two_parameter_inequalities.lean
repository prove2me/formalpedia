-- Prove2me | Theorems.Thm_PerspEpi_lemma_5_prox_two_parameter_inequalities
-- name    : PerspEpi.lemma_5_prox_two_parameter_inequalities
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:40.251927+00:00
-- url     : https://prove2.me/theorems/0b150f0d-8ac2-4a36-9958-6eda2c62c345
-- title:
--   Lemma 5: the two-parameter proximal inequalities (21) and (22)
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $f\in\Gamma_0(E)$, and fix $\lambda,\mu > 0$. Then for every $x\in E$, the values $f(P_\lambda f(x))$, $f(P_\mu f(x))$ are finite and
--
--   $$
--   \frac1{2\mu}\Big(\|P_\mu f(x)-x\|^2 - \|P_\lambda f(x) - x\|^2 + \|P_\mu f(x) - P_\lambda f(x)\|^2\Big) \le f(P_\lambda f(x)) - f(P_\mu f(x))
--   $$
--   $$
--   \le \frac1{2\lambda}\Big(\|P_\mu f(x)-x\|^2 - \|P_\lambda f(x) - x\|^2 - \|P_\mu f(x) - P_\lambda f(x)\|^2\Big), \tag{21}
--   $$
--
--   and
--
--   $$
--   \|P_\lambda f(x) - P_\mu f(x)\|^2 \le \frac{\mu-\lambda}{\lambda+\mu}\Big(\|P_\mu f(x)-x\|^2 - \|P_\lambda f(x)-x\|^2\Big). \tag{22}
--   $$
--
--   These inequalities drive the monotonicity of the proximal value (Corollary 10) and the Lipschitz estimates in $\lambda$ (Corollary 7).
--
--   **Formalization Note** The middle term of (21) is computed with the real values of $f$ at the two proximal points, whose finiteness is part of the statement.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - encoding: f(P_λ f(x)) − f(P_µ f(x)) (finite values) → finiteness of both values, then EReal.toReal of each; reason: proximal points lie in dom f; the extra finiteness clause is true and makes toReal faithful
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Lemma 5, p.15, (21)–(22)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_PerspEpi_prox

open Filter Topology

namespace PerspEpi

/-- **Lemma 5**, inequalities (21) and (22). Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.15: "Let f ∈ Γ0(E) and fix positive scalars
λ and µ. Then for all x ∈ E,
(1/2µ)(‖P_µ f(x) − x‖² − ‖P_λ f(x) − x‖² + ‖P_µ f(x) − P_λ f(x)‖²) ≤ f(P_λ f(x)) − f(P_µ f(x))
≤ (1/2λ)(‖P_µ f(x) − x‖² − ‖P_λ f(x) − x‖² − ‖P_µ f(x) − P_λ f(x)‖²), (21)
and ‖P_λ f(x) − P_µ f(x)‖² ≤ ((µ − λ)/(λ + µ))(‖P_µ f(x) − x‖² − ‖P_λ f(x) − x‖²). (22)"

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. The values `f(P_λ f(x))`, `f(P_µ f(x))` are finite (proximal points lie in `dom f`); the
statement asserts this and then states (21) for their real values. No sign condition on `µ − λ`. -/
theorem lemma_5_prox_two_parameter_inequalities {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (x : E) :
    f (prox f lam x) ≠ ⊤ ∧ f (prox f μ x) ≠ ⊤ ∧
    -- (21)
    (1 / (2 * μ)) * (‖prox f μ x - x‖ ^ 2 - ‖prox f lam x - x‖ ^ 2 +
        ‖prox f μ x - prox f lam x‖ ^ 2) ≤
      (f (prox f lam x)).toReal - (f (prox f μ x)).toReal ∧
    (f (prox f lam x)).toReal - (f (prox f μ x)).toReal ≤
      (1 / (2 * lam)) * (‖prox f μ x - x‖ ^ 2 - ‖prox f lam x - x‖ ^ 2 -
        ‖prox f μ x - prox f lam x‖ ^ 2) ∧
    -- (22)
    ‖prox f lam x - prox f μ x‖ ^ 2 ≤
      (μ - lam) / (lam + μ) * (‖prox f μ x - x‖ ^ 2 - ‖prox f lam x - x‖ ^ 2) := by sorry

end PerspEpi
