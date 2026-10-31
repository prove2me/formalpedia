-- Prove2me | Theorems.Thm_PerspEpi_proposition_5_prox_convergence
-- name    : PerspEpi.proposition_5_prox_convergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:36.514991+00:00
-- url     : https://prove2.me/theorems/f8e7e0cd-1c47-4a10-8c46-5c68e757e3f1
-- title:
--   Proposition 5: $\lim_{\lambda\downarrow0,\,x\to\bar x}P_\lambda f(x)=P_{\operatorname{cl}(\operatorname{dom} f)}(\bar x)$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $f\in\Gamma_0(E)$ and $\bar x \in E$. Then the proximal map converges, jointly in the point and the parameter, to the projection onto the closure of the domain:
--
--   $$
--   \lim_{\lambda\downarrow 0,\ x\to\bar x} P_\lambda f(x) = P_{\operatorname{cl}(\operatorname{dom} f)}(\bar x).
--   $$
--
--   It generalizes the classical fact $P_\lambda f(x)\to x$ for $x\in\operatorname{dom} f$ and justifies the definition of the extended proximal map $P_f$ at $\lambda = 0$.
--
--   **Formalization Note** The joint limit is along the product filter $\mathcal N(\bar x)\times\mathcal N_{>}(0)$ on $E\times\mathbb R$.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - encoding: lim over λ ↓ 0, x → x̄ → Tendsto along 𝓝 x̄ ×ˢ 𝓝[>] 0; reason: the product filter is the joint limit
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Proposition 5, p.15

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_PerspEpi_prox

open Filter Topology

namespace PerspEpi

/-- **Proposition 5 (Convergence of the proximal map).** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.15:
"Let f ∈ Γ0(E) and x̄ ∈ E. Then lim_{λ↓0, x→x̄} P_λ f(x) = P_cl(dom f)(x̄)."

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. The limit is joint in `(x, λ)`: the filter `𝓝 x̄ ×ˢ 𝓝[>] 0` on `E × ℝ`. -/
theorem proposition_5_prox_convergence {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (xbar : E) :
    Tendsto (fun q : E × ℝ => prox f q.2 q.1) (𝓝 xbar ×ˢ 𝓝[>] 0)
      (𝓝 (projC (closure (AubinLipschitz.effDom f)) xbar)) := by sorry

end PerspEpi
