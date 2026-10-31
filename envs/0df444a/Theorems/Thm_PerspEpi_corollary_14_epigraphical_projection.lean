-- Prove2me | Theorems.Thm_PerspEpi_corollary_14_epigraphical_projection
-- name    : PerspEpi.corollary_14_epigraphical_projection
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:13.60836+00:00
-- url     : https://prove2.me/theorems/abf3be5f-9cab-4b58-8e52-81180cf13098
-- title:
--   Corollary 14: the projection onto $\operatorname{epi} f$ is $(P_{\bar\lambda}f(\bar x),\bar\alpha+\bar\lambda)$ at the unique root $\bar\lambda$ of $f(P_\lambda f(\bar x))-\lambda-\bar\alpha$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $f\in\Gamma_0(E)$ a proper closed convex function $E\to\mathbb R\cup\{+\infty\}$, and $(\bar x,\bar\alpha)\in E\times\mathbb R$, where $E\times\mathbb R$ carries the Euclidean norm $\|(x,\alpha)\|^2 = \|x\|^2+\alpha^2$. Write $C = \operatorname{cl}(\operatorname{dom} f)$, $p = P_C(\bar x)$, $\bar\varphi = \bar\varphi^f_{\bar x}$ (display (27)) and
--
--   $$
--   \theta(\lambda) = \bar\varphi(\lambda) + \bar\alpha\lambda + \tfrac12\lambda^2 .
--   $$
--
--   1. **(a) Dual representation of the distance to the epigraph.** The minimum of $\theta$ over $\lambda\ge0$ is attained and
--   $$
--   \tfrac12 d^2_{\operatorname{epi} f}(\bar x,\bar\alpha) = -\min_{\lambda\ge0}\theta(\lambda).
--   $$
--   2. The function $0<\lambda\mapsto f(P_\lambda f(\bar x))-\lambda-\bar\alpha$ is (finite and) strictly decreasing.
--   3. **(b) Projection onto the epigraph.** If $f(p)\le\bar\alpha$, then $P_{\operatorname{epi} f}(\bar x,\bar\alpha) = (p,\bar\alpha)$.
--   4. Otherwise ($f(p)>\bar\alpha$, possibly $f(p)=+\infty$): $\theta$ is finite on $[0,\infty)$ and strongly convex there ($\theta(\lambda)-\frac12\lambda^2$ is convex); it has a unique minimizer $\bar\lambda$ over $\lambda\ge0$; $\bar\lambda>0$;
--   $$
--   P_{\operatorname{epi} f}(\bar x,\bar\alpha) = \big(P_{\bar\lambda}f(\bar x),\ \bar\alpha+\bar\lambda\big);
--   $$
--   and $\bar\lambda$ is the unique root on $(0,\infty)$ of $\lambda\mapsto f(P_\lambda f(\bar x))-\lambda-\bar\alpha$.
--
--   The result reduces the projection onto the epigraph of an arbitrary closed proper convex function, possibly with a proper domain, to a scalar root-finding problem whose evaluations are proximal points; it extends Beck's Theorem 6.36 beyond finite-valued $f$.
--
--   **Formalization Note** $E\times\mathbb R$ is `WithLp 2 (E × ℝ)`; $P_{\operatorname{epi} f}$ and $d_{\operatorname{epi} f}$ are the nearest-point map and the distance there. $\theta$ takes values in `EReal`, and the strict decrease is stated in `EReal`.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - encoding: P_{epi f}(x̄), [u, t], 'λ is the unique root' → projC (epiL2 f) (x̄, ᾱ), the pair (u, t) ∈ WithLp 2 (E × ℝ), λ̄ is the unique positive root; reason: notation: the projected point is (x̄, ᾱ), brackets denote pairs, and the root is the λ̄ of the preceding sentence
--   - encoding: E × ℝ with the Euclidean norm → WithLp 2 (E × ℝ); reason: Lean's E × ℝ has the sup norm, under which the nearest point differs
--   - encoding: strongly convex optimization problem min_{λ≥0} ½λ² + ᾱλ + φ̄(λ) → θ finite on [0, ∞) and λ ↦ θ(λ).toReal − ½λ² ConvexOn [0, ∞); reason: strong convexity with modulus 1 on the feasible set; finiteness makes toReal faithful
--   - reading: 'where λ̄ > 0 … Equivalently, … strictly decreasing function' after the two-case display → the minimizer/root clauses in the second case; strict decrease of λ ↦ f(P_λ f(x̄)) − λ − ᾱ in both cases; reason: in the first case the function is negative on (0, ∞) and has no root, so λ̄ belongs to the second case; strict decrease is a property of the function, not of the case
--   - encoding: e_λ f defined as a min → the infimum ⨅ in EReal (MoreauChance.Consistency.moreauEnv); reason: for f ∈ Γ0(E) and λ > 0 the minimum is attained, so the value is the same
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Corollary 14, p.24

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_PerspEpi_prox
import Definitions.Def_PerspEpi_epiL2
import Definitions.Def_PerspEpi_phiBar

open Filter Topology

namespace PerspEpi

/-- **Corollary 14 (Epigraphical projection).** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.24: "Let f ∈ Γ0(E) and (x̄, ᾱ) ∈ E × ℝ.
Then the following statements hold.
(a) (Dual representation of distance to epigraph) ½d²_{epi f}(x̄, ᾱ) = −min_{λ≥0} {φ̄^f_x̄(λ) + ᾱλ + ½λ²}.
(b) (Projection onto epigraph) P_{epi f}(x̄) = [P_cl(dom f)(x̄), ᾱ] if f(P_cl(dom f)(x̄)) ≤ ᾱ;
[P_λ̄ f(x̄), ᾱ + λ̄] otherwise, where λ̄ > 0 is the unique solution of the strongly convex
optimization problem min_{λ≥0} ½λ² + ᾱλ + φ̄^f_x̄(λ). Equivalently, λ is the unique root of the
strictly decreasing function 0 < λ ↦ f(P_λ f(x̄)) − λ − ᾱ."

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. `E × ℝ` is the Euclidean space `WithLp 2 (E × ℝ)` (`‖(x, α)‖² = ‖x‖² + α²`), `epi f` is
`PerspEpi.epiL2 f`, `P_{epi f}(x̄, ᾱ)` is `projC (epiL2 f) (x̄, ᾱ)` and `d_{epi f}` is
`Metric.infDist` there. `θ(λ) = φ̄^f_x̄(λ) + ᾱλ + ½λ²` in `EReal` (`PerspEpi.phiBar`, display (27)).
(a) asserts that the minimum over `λ ≥ 0` is attained. The strict decrease of
`λ ↦ f(P_λ f(x̄)) − λ − ᾱ` on `(0, ∞)` is stated in `EReal` (it forces `f(P_λ f(x̄))` finite) and in
both cases. In the second case: the minimizer of `θ` over `λ ≥ 0` is unique, positive, gives the
projection, and is the unique positive root; "strongly convex" is stated as: `θ` is finite on
`[0, ∞)` and `λ ↦ θ(λ) − ½λ²` is convex there. -/
theorem corollary_14_epigraphical_projection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (xbar : E) (abar : ℝ) :
    let p : E := projC (closure (AubinLipschitz.effDom f)) xbar
    let θ : ℝ → EReal := fun lam => phiBar f xbar lam + ((abar * lam + (1 / 2) * lam ^ 2 : ℝ) : EReal)
    let IsMin : ℝ → Prop := fun l => 0 ≤ l ∧ ∀ m : ℝ, 0 ≤ m → θ l ≤ θ m
    -- (a)
    (∃ l₀ : ℝ, IsMin l₀ ∧
      (((1 / 2) * Metric.infDist (WithLp.toLp 2 (xbar, abar)) (epiL2 f) ^ 2 : ℝ) : EReal) = -θ l₀) ∧
    -- strict decrease of the root function
    StrictAntiOn (fun lam : ℝ => f (prox f lam xbar) - ((lam + abar : ℝ) : EReal)) (Set.Ioi 0) ∧
    -- (b), first case
    (f p ≤ (abar : EReal) →
      projC (epiL2 f) (WithLp.toLp 2 (xbar, abar)) = WithLp.toLp 2 (p, abar)) ∧
    -- (b), second case
    ((abar : EReal) < f p →
      (∀ lam : ℝ, 0 ≤ lam → θ lam ≠ ⊤) ∧
      ConvexOn ℝ (Set.Ici 0) (fun lam : ℝ => (θ lam).toReal - (1 / 2) * lam ^ 2) ∧
      ∃ lbar : ℝ, IsMin lbar ∧ (∀ l : ℝ, IsMin l → l = lbar) ∧ 0 < lbar ∧
        projC (epiL2 f) (WithLp.toLp 2 (xbar, abar)) =
          WithLp.toLp 2 (prox f lbar xbar, abar + lbar) ∧
        f (prox f lbar xbar) - ((lbar + abar : ℝ) : EReal) = 0 ∧
        (∀ lam : ℝ, 0 < lam → f (prox f lam xbar) - ((lam + abar : ℝ) : EReal) = 0 →
          lam = lbar)) := by sorry

end PerspEpi
