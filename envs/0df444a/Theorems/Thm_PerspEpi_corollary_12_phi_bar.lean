-- Prove2me | Theorems.Thm_PerspEpi_corollary_12_phi_bar
-- name    : PerspEpi.corollary_12_phi_bar
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:57.434302+00:00
-- url     : https://prove2.me/theorems/1e696655-b3a3-4c6e-af18-fbff4bf5cc67
-- title:
--   Corollary 12 (corrected: continuity on $\operatorname{dom}\bar\varphi$; (b) generalized to $P_C(\bar x)\in\operatorname{dom} f$): properties of $\bar\varphi^f_{\bar x}$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $f\in\Gamma_0(E)$, $\bar x\in E$, $C = \operatorname{cl}(\operatorname{dom} f)$, and let $\bar\varphi = \bar\varphi^f_{\bar x}$ be the function of display (27). Then:
--
--   1. **(a)** $\bar\varphi$ is proper and convex, and it is continuous relative to its domain $\operatorname{dom}\bar\varphi$, hence continuous on $\mathbb R$ whenever $P_C(\bar x)\in\operatorname{dom} f$. It is finite and continuously differentiable on $\mathbb R_{++}$ with
--   $$
--   \frac{d}{d\lambda}\bar\varphi(\lambda) = -f(P_\lambda f(\bar x)) \qquad(\lambda>0),
--   $$
--   and this derivative is locally Lipschitz on $\mathbb R_{++}$.
--   2. **(b)** If $P_C(\bar x)\in\operatorname{dom} f$ (in particular if $\bar x\in\operatorname{dom} f$), then $\bar\varphi$ is finite and continuously differentiable on $\mathbb R$ with
--   $$
--   \frac{d}{d\lambda}\bar\varphi(\lambda) = -\eta^f_{\bar x}(\lambda) = \begin{cases} -f(P_\lambda f(\bar x)) & \lambda>0,\\ -f(P_C(\bar x)) & \lambda\le 0.\end{cases}
--   $$
--   If $\bar x\in\operatorname{dom}\partial f$, this derivative is locally Lipschitz on all of $\mathbb R$.
--   3. **(c)** If $P_C(\bar x)\notin\operatorname{dom} f$, then $\operatorname{dom}\bar\varphi = \mathbb R_+$ and
--   $$
--   \partial\bar\varphi(\lambda) = \begin{cases} \{-f(P_\lambda f(\bar x))\} & \lambda>0,\\ \emptyset & \lambda\le0.\end{cases}
--   $$
--
--   The corollary identifies the proximal value function as the negative derivative of a convex function, which turns the root-finding problem of Corollary 14 into a strongly convex minimization over $\lambda\ge0$.
--
--   **Formalization Note** Proper means never $-\infty$ and somewhere finite; convexity is convexity of the epigraph in $\mathbb R\times\mathbb R$. Derivatives are those of the real function $\lambda\mapsto\bar\varphi(\lambda)$ where it is finite; "continuously differentiable" is $C^1$.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - correction: (a) φ̄ continuous (possibly in an extended real-valued sense) on ℝ → φ̄ continuous on dom φ̄, and continuous on ℝ when P_cl(dom f)(x̄) ∈ dom f; reason: the printed claim is false in case (c): for f = −log on (0,∞) (+∞ elsewhere) and x̄ = 0, φ̄ = +∞ on λ < 0 but φ̄(λ) → 0 = φ̄(0) as λ ↓ 0; the proof shows continuity on the domain
--   - generalization: (b) hypothesis x̄ ∈ dom f → hypothesis P_cl(dom f)(x̄) ∈ dom f; reason: the proof of (b) assumes only this and Proposition 8 uses (b) under it; x̄ ∈ dom f gives P_cl(dom f)(x̄) = x̄ ∈ dom f, so the printed (b) is a special case
--   - encoding: continuously differentiable with derivative …; derivative locally Lipschitz → finiteness, ContDiffOn ℝ 1 / ContDiff ℝ 1 and HasDerivAt of λ ↦ (φ̄ λ).toReal; LocallyLipschitzOn of the real derivative; reason: differentiability presupposes finite values; the finiteness clauses are true and make toReal faithful
--   - encoding: e_λ f defined as a min → the infimum ⨅ in EReal (MoreauChance.Consistency.moreauEnv); reason: for f ∈ Γ0(E) and λ > 0 the minimum is attained, so the value is the same
--   - encoding: proper; convex; (c) ∂φ̄(λ) = −f(P_λ f(x̄)) for λ > 0 → never ⊥ and somewhere ≠ ⊤; Convex of the epigraph in ℝ × ℝ; the singleton {−(f(P_λ f(x̄))).toReal}; reason: the definitions of p.4 for an EReal-valued function; ∂φ̄(λ) is a set whose only element is the printed value, which is finite
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Corollary 12, p.20

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_PerspEpi_prox
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_PerspEpi_eta
import Definitions.Def_PerspEpi_phiBar

open Filter Topology

namespace PerspEpi

/-- **Corollary 12 (The function φ̄^f_x̄)**, with the continuity claim of (a) corrected and the
hypothesis of (b) generalized. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.20: "Let f ∈ Γ0(E) and fix x̄ ∈ E. Then the following hold:
(a) φ̄^f_x̄ is proper, convex and continuous (possibly in an extended real-valued sense), and
continuously differentiable on ℝ₊₊ with (d/dλ) φ̄^f_x̄(λ) = −f(P_λ f(x̄)) locally Lipschitz for all
λ > 0. (b) If x̄ ∈ dom f, then φ̄^f_x̄ is continuously differentiable on ℝ with derivative given by
(d/dλ) φ̄^f_x̄(λ) = −η^f_x̄(λ) = −f(P_λ f(x̄)) if λ > 0; −f(P_cl(dom f)(x̄)) if λ ≤ 0. If, more
strictly, x̄ ∈ dom ∂f, then this derivative is locally Lipschitz on all of ℝ.
(c) If P_cl(dom f)(x̄) ∉ dom f, then dom φ̄^f_x̄ = ℝ₊ and
∂φ̄^f_x̄(λ) = −f(P_λ f(x̄)) if λ > 0; ∅ if λ ≤ 0."

**Correction of (a).** Continuity in the `EReal` topology fails in case (c): for `f = −log` on
`(0, ∞)` (`+∞` elsewhere) and `x̄ = 0`, `φ̄ = +∞` on `λ < 0` but `φ̄(λ) → 0 = φ̄(0)` as `λ ↓ 0`. The
statement here is continuity relative to `dom φ̄` (what the proof shows), plus continuity on all of
`ℝ` whenever `P_cl(dom f)(x̄) ∈ dom f` (then `dom φ̄ = ℝ`).
**Generalization of (b).** The hypothesis `x̄ ∈ dom f` is replaced by the weaker
`P_cl(dom f)(x̄) ∈ dom f` (the proof of (b) assumes only this, and Proposition 8 uses (b) under it).
For `x̄ ∈ dom f`, `P_cl(dom f)(x̄) = x̄`, so the printed (b) is a special case.

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. `φ̄^f_x̄` is `PerspEpi.phiBar f x̄ : ℝ → EReal` (display (27)); proper = never `⊥` and
somewhere `≠ ⊤`; convex = convex epigraph in `ℝ × ℝ`; `dom φ̄ = {λ | φ̄(λ) ≠ ⊤}`. Derivatives are
of the real function `λ ↦ φ̄(λ).toReal` on the open set where `φ̄` is finite; "continuously
differentiable" is `ContDiffOn ℝ 1`. `∂φ̄` is the convex subdifferential on `ℝ` (`MoreauChance.Consistency.subdiff`). -/
theorem corollary_12_phi_bar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (xbar : E) :
    -- (a)
    ((∀ lam : ℝ, phiBar f xbar lam ≠ ⊥) ∧ (∃ lam : ℝ, phiBar f xbar lam ≠ ⊤) ∧
      Convex ℝ {p : ℝ × ℝ | phiBar f xbar p.1 ≤ (p.2 : EReal)} ∧
      ContinuousOn (phiBar f xbar) (AubinLipschitz.effDom (phiBar f xbar)) ∧
      (projC (closure (AubinLipschitz.effDom f)) xbar ∈ AubinLipschitz.effDom f → Continuous (phiBar f xbar)) ∧
      (∀ lam : ℝ, 0 < lam → phiBar f xbar lam ≠ ⊤) ∧
      ContDiffOn ℝ 1 (fun lam : ℝ => (phiBar f xbar lam).toReal) (Set.Ioi 0) ∧
      (∀ lam : ℝ, 0 < lam → HasDerivAt (fun l : ℝ => (phiBar f xbar l).toReal)
        (-(f (prox f lam xbar)).toReal) lam) ∧
      LocallyLipschitzOn (Set.Ioi 0) (fun lam : ℝ => -(f (prox f lam xbar)).toReal)) ∧
    -- (b)
    (projC (closure (AubinLipschitz.effDom f)) xbar ∈ AubinLipschitz.effDom f →
      (∀ lam : ℝ, phiBar f xbar lam ≠ ⊤) ∧
      ContDiff ℝ 1 (fun lam : ℝ => (phiBar f xbar lam).toReal) ∧
      (∀ lam : ℝ, HasDerivAt (fun l : ℝ => (phiBar f xbar l).toReal)
        (-(eta f xbar lam).toReal) lam)) ∧
    ((MoreauChance.Consistency.subdiff f xbar).Nonempty →
      LocallyLipschitz (fun lam : ℝ => -(eta f xbar lam).toReal)) ∧
    -- (c)
    (projC (closure (AubinLipschitz.effDom f)) xbar ∉ AubinLipschitz.effDom f →
      AubinLipschitz.effDom (phiBar f xbar) = Set.Ici 0 ∧
      ∀ lam : ℝ, MoreauChance.Consistency.subdiff (phiBar f xbar) lam =
        if 0 < lam then {-(f (prox f lam xbar)).toReal} else ∅) := by sorry

end PerspEpi
