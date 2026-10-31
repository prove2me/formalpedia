-- Prove2me | Theorems.Thm_PerspEpi_corollary_7_prox_lipschitz
-- name    : PerspEpi.corollary_7_prox_lipschitz
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:35.310621+00:00
-- url     : https://prove2.me/theorems/0b358cb5-9111-4141-89f4-b3c01fcf8e24
-- title:
--   Corollary 7: continuity and local Lipschitz continuity of $P_f$, calmness (23a)–(23b) at $(\bar x,0)$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $f\in\Gamma_0(E)$, and let $P_f$ be the extended proximal map ($P_\lambda f(x)$ for $\lambda>0$, $P_{\operatorname{cl}(\operatorname{dom} f)}(x)$ for $\lambda=0$, $\emptyset$ for $\lambda<0$). Then:
--
--   1. $\operatorname{dom} P_f = E\times\mathbb R_+$, $P_f$ is single-valued there, and it is continuous on $E\times\mathbb R_+$;
--   2. $P_f$ is locally Lipschitz on $\operatorname{int}(\operatorname{dom} P_f) = E\times\mathbb R_{++}$;
--   3. if $\bar x \in \operatorname{dom}\partial f$, there are $\kappa,\varepsilon>0$ with
--   $$
--   \|P_f(\bar x,0) - P_f(x,\lambda)\| \le \kappa\|(\bar x - x,\lambda)\| \quad \forall (x,\lambda)\in B_\varepsilon(\bar x,0)\cap\operatorname{dom}P_f, \tag{23a}
--   $$
--   $$
--   \|P_f(\bar x,\lambda) - P_f(\bar x,\mu)\| \le \kappa|\mu-\lambda| \quad \forall \lambda,\mu\in[0,\varepsilon]. \tag{23b}
--   $$
--
--   (23a) is calmness (upper Lipschitz continuity) of $P_f$ at $(\bar x,0)$ and (23b) local Lipschitz continuity of $\mu\mapsto P_f(\bar x,\mu)$ at $0$; they are the input to the local Lipschitz continuity of the proximal value on all of $\mathbb R$ (Corollary 11(c)).
--
--   **Formalization Note** The single value of $P_f$ on $\lambda\ge0$ is written as a function $s(x,\lambda)$. In (23a) the norm and the ball are Euclidean, $\sqrt{\|\bar x-x\|^2+\lambda^2}$ and $\|\bar x-x\|^2+\lambda^2\le\varepsilon^2$.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - encoding: P_f : E × ℝ ⇉ E continuous / locally Lipschitz on its domain → extProx f with dom = {λ ≥ 0}, equal to {s q} there; continuity and LocallyLipschitzOn of the selection s; reason: a map that is single-valued on its domain is continuous / Lipschitz exactly when its selection is
--   - encoding: locally Lipschitz on int(dom P_f) with the Euclidean norm of E × ℝ → LocallyLipschitzOn {λ > 0} for the product (max) metric of E × ℝ; reason: the two norms are equivalent and the Lipschitz constants are existential
--   - encoding: B_ε(x̄,0) → closed Euclidean ball ‖x̄ − x‖² + λ² ≤ ε²; reason: ε is existential, so open and closed balls give the same claim
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Corollary 7, p.16, (23a)–(23b)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_PerspEpi_prox
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_PerspEpi_extProx

open Filter Topology

namespace PerspEpi

/-- **Corollary 7 (Lipschitz continuity of the proximal map).** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.16: "Let f ∈ Γ0(E). Then
P_f is continuous on dom P_f = E × ℝ₊ and is locally Lipschitz on int(dom P_f). If x̄ ∈ dom ∂f, then
P_f is upper Lipschitz (or calm) at (x̄,0), and the map ℝ₊ ∋ µ ↦ P_f(x̄,µ) is locally Lipschitz at 0,
i.e., there exist positive scalars κ and ε such that
‖P_f(x̄,0) − P_f(x,λ)‖ ≤ κ‖(x̄ − x,λ)‖ ∀(x,λ) ∈ B_ε(x̄,0) ∩ dom P_f, (23a)
‖P_f(x̄,λ) − P_f(x̄,µ)‖ ≤ κ|µ − λ| ∀λ,µ ∈ [0,ε]. (23b)"

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. `P_f` is the set-valued `PerspEpi.extProx`; the statement says its domain is
`{λ ≥ 0}`, that it is single-valued there with value `s(x, λ)` (`P_λ f(x)` for `λ > 0`,
`P_cl(dom f)(x)` for `λ = 0`), and states continuity and the Lipschitz properties for `s`.
"Locally Lipschitz on int(dom P_f)" uses the product metric of `E × ℝ`, which is equivalent to the
Euclidean one (the Lipschitz constants are existential). In (23a) the norm `‖(x̄ − x, λ)‖` and the
ball `B_ε(x̄, 0)` are Euclidean: `√(‖x̄ − x‖² + λ²)` and `‖x̄ − x‖² + λ² ≤ ε²`. `dom ∂f` is
`{x | ∂f(x) ≠ ∅}`. -/
theorem corollary_7_prox_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) :
    let s : E × ℝ → E := fun q =>
      if 0 < q.2 then prox f q.2 q.1 else projC (closure (AubinLipschitz.effDom f)) q.1
    (∀ q : E × ℝ, (extProx f q).Nonempty ↔ 0 ≤ q.2) ∧
    (∀ q : E × ℝ, 0 ≤ q.2 → extProx f q = {s q}) ∧
    ContinuousOn s {q : E × ℝ | 0 ≤ q.2} ∧
    LocallyLipschitzOn {q : E × ℝ | 0 < q.2} s ∧
    (∀ xbar : E, (MoreauChance.Consistency.subdiff f xbar).Nonempty →
      ∃ κ > (0 : ℝ), ∃ ε > (0 : ℝ),
        -- (23a)
        (∀ (x : E) (lam : ℝ), 0 ≤ lam → ‖xbar - x‖ ^ 2 + lam ^ 2 ≤ ε ^ 2 →
          ‖s (xbar, 0) - s (x, lam)‖ ≤ κ * Real.sqrt (‖xbar - x‖ ^ 2 + lam ^ 2)) ∧
        -- (23b)
        (∀ lam ∈ Set.Icc (0 : ℝ) ε, ∀ μ ∈ Set.Icc (0 : ℝ) ε,
          ‖s (xbar, lam) - s (xbar, μ)‖ ≤ κ * |μ - lam|)) := by sorry

end PerspEpi
