-- Prove2me | Theorems.Thm_PerspEpi_corollary_10_prox_value_monotonicity
-- name    : PerspEpi.corollary_10_prox_value_monotonicity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:13.480172+00:00
-- url     : https://prove2.me/theorems/8cb24eb1-33e7-4589-b75d-0b0c3a4ced57
-- title:
--   Corollary 10: $\lambda\mapsto f(P_\lambda f(\bar x))$ is nonincreasing, $\lambda\mapsto\|\bar x-P_\lambda f(\bar x)\|$ nondecreasing, limit at $0$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $f\in\Gamma_0(E)$ and $\bar x\in E$. Then
--
--   1. **(a)** $0<\lambda\mapsto f(P_\lambda f(\bar x))$ is decreasing (nonincreasing), i.e. increasing as $\lambda\downarrow0$;
--   2. **(b)** $0<\lambda\mapsto\|\bar x-P_\lambda f(\bar x)\|$ is increasing (nondecreasing);
--   3. **(c)** $$\lim_{\lambda\downarrow0} f(P_\lambda f(\bar x)) = f\big(P_{\operatorname{cl}(\operatorname{dom} f)}(\bar x)\big),$$ where the right-hand side may be $+\infty$.
--
--   These are the monotonicity and boundary behaviour of the proximal value function $\eta^f_{\bar x}$ used in Corollaries 11 and 12.
--
--   **Formalization Note** The limit in (c) is taken in `EReal`.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - reading: decreasing / increasing → AntitoneOn / MonotoneOn on (0, ∞) (non-strict); reason: Example 2 (p.18) has f(P_λ f(2)) ≡ 1 on (0,1], so strict monotonicity is false; the paper uses the words non-strictly
--   - encoding: lim_{λ→0} over λ > 0 → Tendsto along 𝓝[>] 0 in EReal; reason: the map is only defined for λ > 0; the limit may be +∞
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Corollary 10, pp.18–19

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_PerspEpi_prox

open Filter Topology

namespace PerspEpi

/-- **Corollary 10 (Monotonicity and continuity in λ).** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, pp.18–19: "Let f ∈ Γ0(E) and fix
x̄ ∈ E. Then (a) 0 < λ ↦ f(P_λ f(x̄)) is decreasing (i.e., increasing as λ ↓ 0);
(b) 0 < λ ↦ ‖x̄ − P_λ f(x̄)‖ is increasing; (c) lim_{λ→0} f(P_λ f(x̄)) = f(P_cl(dom f)(x̄))."

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. "decreasing"/"increasing" are non-strict (`AntitoneOn`/`MonotoneOn` on `(0, ∞)`): in the
paper's Example 2 (p.18), `f(P_λ f(2)) ≡ 1` on `(0, 1]`. (c) is the one-sided limit `λ ↓ 0` in
`EReal`; the right side may be `+∞`. -/
theorem corollary_10_prox_value_monotonicity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (xbar : E) :
    AntitoneOn (fun lam : ℝ => f (prox f lam xbar)) (Set.Ioi 0) ∧
    MonotoneOn (fun lam : ℝ => ‖xbar - prox f lam xbar‖) (Set.Ioi 0) ∧
    Tendsto (fun lam : ℝ => f (prox f lam xbar)) (𝓝[>] 0)
      (𝓝 (f (projC (closure (AubinLipschitz.effDom f)) xbar))) := by sorry

end PerspEpi
